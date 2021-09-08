/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.translator;

import static edu.mit.csail.sdg.alloy4.Util.tail;
import static edu.mit.csail.sdg.ast.Sig.UNIV;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ConstMap;
import edu.mit.csail.sdg.alloy4.Env;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.CommandScope;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Type;
import edu.mit.csail.sdg.ast.VisitReturn;
import kodkod.ast.BinaryExpression;
import kodkod.ast.Decls;
import kodkod.ast.ExprToIntCast;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IntConstant;
import kodkod.ast.IntExpression;
import kodkod.ast.IntToExprCast;
import kodkod.ast.QuantifiedFormula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.ast.operator.ExprOperator;
import kodkod.engine.CapacityExceededException;
import kodkod.engine.fol2sat.HigherOrderDeclException;
import kodkod.engine.ltl2fol.TemporalTranslator;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.util.ints.IntVector;

/**
 * Translate an Alloy AST into Kodkod AST then attempt to solve it using Kodkod.
 *
 * @modified [electrum] added the translation of temporal operators and
 *           quantifies globally over time constraints over sigs and fields (sig
 *           facts are also implicitly globally quantified); also, variable
 *           singleton sigs are not collapsed like static ones; name all
 *           relations of total order; updated reporting
 */

public final class TranslateAlloyToKodkod extends VisitReturn<Object> {

    static int                                cnt              = 0;

    /**
     * This is used to detect "function recursion" (which we currently do not
     * allow); also, by knowing the current function name, we can provide a more
     * meaningful name for skolem variables
     */
    private final List<Func>                  current_function = new ArrayList<Func>();

    /**
     * This maps the current local variables (LET, QUANT, Function Param) to the
     * actual Kodkod Expression/IntExpression/Formula.
     */
    private Env<ExprVar,Object>               env              = new Env<ExprVar,Object>();

    /**
     * If frame!=null, it stores the scope, bounds, and other settings necessary for
     * performing a solve.
     */
    private final A4Solution                  frame;

    /**
     * If frame==null, it stores the mapping from each Sig/Field/Skolem/Atom to its
     * corresponding Kodkod expression.
     */
    private final ConstMap<Expr,Expression>   a2k;

    /**
     * If frame==null, it stores the mapping from each String literal to its
     * corresponding Kodkod expression.
     */
    private final ConstMap<String,Expression> s2k;

    /** The current reporter. */
    private A4Reporter                        rep;

    /** If nonnull, it's the current command. */
    private final Command                     cmd;

    /** The bitwidth. */
    private final int                         bitwidth;

    /** The minimum allowed integer. */
    private final int                         min;

    /** The maximum allowed integer. */
    private final int                         max;

    /** The maximum allowed loop unrolling and recursion. */
    private final int                         unrolls;

    /**
     * Construct a translator based on the given list of sigs and the given command.
     *
     * @param rep - if nonnull, it's the reporter that will receive diagnostics and
     *            progress reports
     * @param opt - the solving options (must not be null)
     * @param sigs - the list of sigs (must not be null, and must be a complete
     *            list)
     * @param cmd - the command to solve (must not be null)
     */
    private TranslateAlloyToKodkod(A4Reporter rep, A4Options opt, Iterable<Sig> sigs, Command cmd) throws Err {
        this.unrolls = opt.unrolls;
        this.rep = (rep != null) ? rep : A4Reporter.NOP;
        this.cmd = cmd;
        Pair<A4Solution,ScopeComputer> pair = ScopeComputer.compute(this.rep, opt, sigs, cmd);
        this.frame = pair.a;
        this.bitwidth = pair.a.getBitwidth();
        this.min = pair.a.min();
        this.max = pair.a.max();
        this.a2k = null;
        this.s2k = null;
        BoundsComputer.compute(rep, frame, pair.b, sigs);
    }

    /**
     * Construct a translator based on a already-fully-constructed association map.
     *
     * @param bitwidth - the integer bitwidth to use
     * @param unrolls - the maximum number of loop unrolling and recursion allowed
     * @param a2k - the mapping from Alloy sig/field/skolem/atom to the
     *            corresponding Kodkod expression
     */
    private TranslateAlloyToKodkod(int bitwidth, int unrolls, Map<Expr,Expression> a2k, Map<String,Expression> s2k) throws Err {
        this.unrolls = unrolls;
        if (bitwidth < 0)
            throw new ErrorSyntax("Cannot specify a bitwidth less than 0");
        if (bitwidth > 30)
            throw new ErrorSyntax("Cannot specify a bitwidth greater than 30");
        this.rep = A4Reporter.NOP;
        this.cmd = null;
        this.frame = null;
        this.bitwidth = bitwidth;
        this.max = Util.max(bitwidth);
        this.min = Util.min(bitwidth);
        this.a2k = ConstMap.make(a2k);
        this.s2k = ConstMap.make(s2k);
    }

    /**
     * Associate the given formula with the given expression, then return the
     * formula as-is.
     */
    private Formula k2pos(Formula f, Expr e) throws Err {
        if (k2pos_enabled)
            if (frame != null)
                frame.k2pos(f, e);
        return f;
    }

    private boolean k2pos_enabled = true;

    /**
     * Returns the expression corresponding to the given sig.
     */
    private Expression a2k(Sig x) throws Err {
        if (a2k != null)
            return a2k.get(x);
        else
            return frame.a2k(x);
    }

    /**
     * Returns the expression corresponding to the given field.
     */
    private Expression a2k(Field x) throws Err {
        if (a2k != null)
            return a2k.get(x);
        else
            return frame.a2k(x);
    }

    /**
     * Returns the expression corresponding to the given skolem/atom.
     */
    private Expression a2k(ExprVar x) throws Err {
        if (a2k != null)
            return a2k.get(x);
        else
            return frame.a2k(x);
    }

    /**
     * Returns the expression corresponding to the given string literal.
     */
    private Expression s2k(String x) throws Err {
        if (s2k != null)
            return s2k.get(x);
        else
            return frame.a2k(x);
    }

    // ==============================================================================================================//

    /**
     * Stores the list of "totalOrder predicates" that we constructed.
     */
    private final List<Relation> totalOrderPredicates = new ArrayList<Relation>();

    /**
     * Conjoin the constraints for "field declarations" and "fact" paragraphs
     */
    private void makeFacts(Expr facts) throws Err {
        rep.debug("Generating facts...\n");
        // convert into a form that hopefully gives better unsat core
        facts = (new ConvToConjunction()).visitThis(facts);
        // add the field facts and appended facts
        for (Sig s : frame.getAllReachableSigs()) {
            for (Decl d : s.getFieldDecls()) {
                k2pos_enabled = false;
                for (ExprHasName n : d.names) {
                    Field f = (Field) n;
                    Expr form = s.decl.get().join(f).in(d.expr);
                    form = s.isOne == null ? form.forAll(s.decl) : ExprLet.make(null, (ExprVar) (s.decl.get()), s, form);
                    Formula ff = cform(form);
                    if (TemporalTranslator.isTemporal(ff))
                        ff = ff.always();
                    frame.addFormula(ff, f);
                    // Given the above, we can be sure that every column is
                    // well-bounded (except possibly the first column).
                    // Thus, we need to add a bound that the first column is a
                    // subset of s.
                    // [electrum] mutable singletons sigs cannot be simplified
                    if (s.isOne == null || s.isVariable != null) {
                        Expression sr = a2k(s), fr = a2k(f);
                        for (int i = f.type().arity(); i > 1; i--)
                            fr = fr.join(Expression.UNIV);
                        ff = fr.in(sr);
                        if (TemporalTranslator.isTemporal(ff))
                            ff = ff.always();
                        frame.addFormula(ff, f);
                    }
                }
                if (s.isOne == null && d.disjoint2 != null)
                    for (ExprHasName f : d.names) {
                        Decl that = s.oneOf("that");
                        Expr formula = s.decl.get().equal(that.get()).not().implies(s.decl.get().join(f).intersect(that.get().join(f)).no());
                        Formula ff = cform(formula.forAll(that).forAll(s.decl));
                        if (d.isVar != null)
                            ff = ff.always();
                        frame.addFormula(ff, d.disjoint2);
                    }
                if (d.names.size() > 1 && d.disjoint != null) {
                    Formula ff = cform(ExprList.makeDISJOINT(d.disjoint, null, d.names));
                    if (d.isVar != null)
                        ff = ff.always();
                    frame.addFormula(ff, d.disjoint);
                }
            }
            k2pos_enabled = true;
            for (Expr f : s.getFacts()) {
                Expr form = s.isOne == null ? f.forAll(s.decl) : ExprLet.make(null, (ExprVar) (s.decl.get()), s, f);
                Formula kdorm = cform(form);
                // [electrum] avoid "always" over statics (not only efficiency, total orders would not by detected in SB)
                if (TemporalTranslator.isTemporal(kdorm))
                    kdorm = kdorm.always();
                frame.addFormula(kdorm, f);
            }
        }
        k2pos_enabled = true;
        recursiveAddFormula(facts);
    }

    /**
     * Break up x into conjuncts then add them each as a fact.
     */
    private void recursiveAddFormula(Expr x) throws Err {
        if (x instanceof ExprList && ((ExprList) x).op == ExprList.Op.AND) {
            for (Expr e : ((ExprList) x).args)
                recursiveAddFormula(e);
        } else {
            frame.addFormula(cform(x), x);
        }
    }

    // ==============================================================================================================//

    private static final class GreedySimulator extends Simplifier {

        private List<Relation> totalOrderPredicates = null;
        private Iterable<Sig>  allSigs              = null;
        private ConstList<Sig> growableSigs         = null;
        private A4Solution     partial              = null;

        public GreedySimulator() {
        }

        private TupleSet convert(TupleFactory factory, Expr f) throws Err {
            TupleSet old = ((A4TupleSet) (partial.eval(f))).debugGetKodkodTupleset();
            TupleSet ans = factory.noneOf(old.arity());
            for (Tuple oldT : old) {
                Tuple newT = null;
                for (int i = 0; i < oldT.arity(); i++) {
                    if (newT == null)
                        newT = factory.tuple(oldT.atom(i));
                    else
                        newT = newT.product(factory.tuple(oldT.atom(i)));
                }
                ans.add(newT);
            }
            return ans;
        }

        @Override
        public boolean simplify(A4Reporter rep, A4Solution sol, List<Formula> unused) throws Err {
            TupleFactory factory = sol.getFactory();
            TupleSet oldUniv = convert(factory, Sig.UNIV);
            Set<Object> oldAtoms = new HashSet<Object>();
            for (Tuple t : oldUniv)
                oldAtoms.add(t.atom(0));
            for (Sig s : allSigs) {
                // The case below is STRICTLY an optimization; the entire
                // statement can be removed without affecting correctness
                if (s.isOne != null && s.getFields().size() == 2)
                    for (int i = 0; i + 3 < totalOrderPredicates.size(); i = i + 4)
                        if (totalOrderPredicates.get(i + 1) == right(sol.a2k(s.getFields().get(0))) && totalOrderPredicates.get(i + 3) == right(sol.a2k(s.getFields().get(1)))) {
                            TupleSet allelem = sol.query(true, totalOrderPredicates.get(i), true);
                            if (allelem.size() == 0)
                                continue;
                            Tuple first = null, prev = null;
                            TupleSet next = factory.noneOf(2);
                            for (Tuple t : allelem) {
                                if (prev == null)
                                    first = t;
                                else
                                    next.add(prev.product(t));
                                prev = t;
                            }
                            try {
                                sol.shrink(totalOrderPredicates.get(i + 1), factory.range(first, first), factory.range(first, first));
                                sol.shrink(totalOrderPredicates.get(i + 2), factory.range(prev, prev), factory.range(prev, prev));
                                sol.shrink(totalOrderPredicates.get(i + 3), next, next);
                            } catch (Throwable ex) {
                                // Error here is not fatal
                            }
                        }
                // The case above is STRICTLY an optimization; the entire
                // statement can be removed without affecting correctness
                for (Field f : s.getFields()) {
                    Expression rel = sol.a2k(f);
                    if (s.isOne != null) {
                        rel = right(rel);
                        if (!(rel instanceof Relation))
                            continue;
                        // Retrieve the old value from the previous solution,
                        // and convert it to the new unverse.
                        // This should always work since the new universe is not
                        // yet solved, and so it should have all possible atoms.
                        TupleSet newLower = convert(factory, s.join(f)), newUpper = newLower.clone();
                        // Bind the partial instance
                        for (Tuple t : sol.query(false, rel, false))
                            for (int i = 0; i < t.arity(); i++)
                                if (!oldAtoms.contains(t.atom(i))) {
                                    newLower.add(t);
                                    break;
                                }
                        for (Tuple t : sol.query(true, rel, false))
                            for (int i = 0; i < t.arity(); i++)
                                if (!oldAtoms.contains(t.atom(i))) {
                                    newUpper.add(t);
                                    break;
                                }
                        sol.shrink((Relation) rel, newLower, newUpper);
                    } else {
                        if (!(rel instanceof Relation))
                            continue;
                        // Retrieve the old value from the previous solution,
                        // and convert it to the new unverse.
                        // This should always work since the new universe is not
                        // yet solved, and so it should have all possible atoms.
                        TupleSet newLower = convert(factory, f), newUpper = newLower.clone();
                        // Bind the partial instance
                        for (Tuple t : sol.query(false, rel, false))
                            for (int i = 0; i < t.arity(); i++)
                                if (!oldAtoms.contains(t.atom(i))) {
                                    newLower.add(t);
                                    break;
                                }
                        for (Tuple t : sol.query(true, rel, false))
                            for (int i = 0; i < t.arity(); i++)
                                if (!oldAtoms.contains(t.atom(i))) {
                                    newUpper.add(t);
                                    break;
                                }
                        sol.shrink((Relation) rel, newLower, newUpper);
                    }
                }
            }
            return true;
        }
    }

    static ErrorType rethrow(CapacityExceededException ex) {
        IntVector vec = ex.dims();
        return new ErrorType("Translation capacity exceeded.\n" + "In this scope, universe contains " + vec.get(0) + " atoms\n" + "and relations of arity " + vec.size() + " cannot be represented.\n" + "Visit http://alloy.mit.edu/ for advice on refactoring.");
    }

    private static A4Solution execute_greedyCommand(A4Reporter rep, Iterable<Sig> sigs, Command usercommand, A4Options opt) throws Exception {
        // FIXTHIS: if the next command has a "smaller scope" than the last
        // command, we would get a Kodkod exception...
        // FIXTHIS: if the solver is "toCNF" or "toKodkod" then this method will
        // throw an Exception...
        // FIXTHIS: does solution enumeration still work when we're doing a
        // greedy solve?
        TranslateAlloyToKodkod tr = null;
        try {
            long start = System.currentTimeMillis();
            GreedySimulator sim = new GreedySimulator();
            sim.allSigs = sigs;
            sim.partial = null;
            A4Reporter rep2 = new A4Reporter(rep) {

                private boolean first = true;

                @Override
                public void translate(String solver, int bitwidth, int maxseq, int mintrace, int maxtrace, int skolemDepth, int symmetry, String strat) {
                    if (first)
                        super.translate(solver, bitwidth, maxseq, mintrace, maxtrace, skolemDepth, symmetry, strat);
                    first = false;
                }

                @Override
                public void resultSAT(Object command, long solvingTime, Object solution) {
                }

                @Override
                public void resultUNSAT(Object command, long solvingTime, Object solution) {
                }
            };
            // Form the list of commands
            List<Command> commands = new ArrayList<Command>();
            while (usercommand != null) {
                commands.add(usercommand);
                usercommand = usercommand.parent;
            }
            // For each command...
            A4Solution sol = null;
            for (int i = commands.size() - 1; i >= 0; i--) {
                Command cmd = commands.get(i);
                sim.growableSigs = cmd.getGrowableSigs();
                while (cmd != null) {
                    rep.debug(cmd.scope.toString());
                    usercommand = cmd;
                    tr = new TranslateAlloyToKodkod(rep2, opt, sigs, cmd);
                    tr.makeFacts(cmd.formula);
                    sim.totalOrderPredicates = tr.totalOrderPredicates;
                    sol = tr.frame.solve(rep2, cmd, sim.partial == null || cmd.check ? new Simplifier() : sim, false);
                    if (!sol.satisfiable() && !cmd.check) {
                        start = System.currentTimeMillis() - start;
                        if (sim.partial == null) {
                            rep.resultUNSAT(cmd, start, sol);
                            return sol;
                        } else {
                            rep.resultSAT(cmd, start, sim.partial);
                            return sim.partial;
                        }
                    }
                    if (sol.satisfiable() && cmd.check) {
                        start = System.currentTimeMillis() - start;
                        rep.resultSAT(cmd, start, sol);
                        return sol;
                    }
                    sim.partial = sol;
                    if (sim.growableSigs.isEmpty())
                        break;
                    for (Sig s : sim.growableSigs) {
                        CommandScope sc = cmd.getScope(s);
                        if (sc.increment > sc.endingScope - sc.startingScope) {
                            cmd = null;
                            break;
                        }
                        cmd = cmd.change(s, sc.isExact, sc.startingScope + sc.increment, sc.endingScope, sc.increment);
                    }
                }
            }
            if (sol.satisfiable())
                rep.resultSAT(usercommand, System.currentTimeMillis() - start, sol);
            else
                rep.resultUNSAT(usercommand, System.currentTimeMillis() - start, sol);
            return sol;
        } catch (CapacityExceededException ex) {
            throw rethrow(ex);
        } catch (HigherOrderDeclException ex) {
            Pos p = tr != null ? tr.frame.kv2typepos(ex.decl().variable()).b : Pos.UNKNOWN;
            throw new ErrorType(p, "Analysis cannot be performed since it requires higher-order quantification that could not be skolemized.");
        }
    }

    /**
     * Based on the specified "options", execute one command and return the
     * resulting A4Solution object.
     *
     * @param rep - if nonnull, we'll send compilation diagnostic messages to it
     * @param sigs - the list of sigs; this list must be complete
     * @param cmd - the Command to execute
     * @param opt - the set of options guiding the execution of the command
     * @return null if the user chose "save to FILE" as the SAT solver, and nonnull
     *         if the solver finishes the entire solving and is either satisfiable
     *         or unsatisfiable.
     *         <p>
     *         If the return value X is satisfiable, you can call X.next() to get
     *         the next satisfying solution X2; and you can call X2.next() to get
     *         the next satisfying solution X3... until you get an unsatisfying
     *         solution.
     */
    public static A4Solution execute_command(A4Reporter rep, Iterable<Sig> sigs, Command cmd, A4Options opt) throws Err {
        if (rep == null)
            rep = A4Reporter.NOP;
        TranslateAlloyToKodkod tr = null;
        try {
            if (cmd.parent != null || !cmd.getGrowableSigs().isEmpty())
                return execute_greedyCommand(rep, sigs, cmd, opt);
            tr = new TranslateAlloyToKodkod(rep, opt, sigs, cmd);
            tr.makeFacts(cmd.formula);
            return tr.frame.solve(rep, cmd, new Simplifier(), false);
        } catch (UnsatisfiedLinkError ex) {
            throw new ErrorFatal("The required JNI library cannot be found: " + ex.toString().trim(), ex);
        } catch (CapacityExceededException ex) {
            throw rethrow(ex);
        } catch (HigherOrderDeclException ex) {
            Pos p = tr != null ? tr.frame.kv2typepos(ex.decl().variable()).b : Pos.UNKNOWN;
            throw new ErrorType(p, "Analysis cannot be performed since it requires higher-order quantification that could not be skolemized.");
        } catch (Throwable ex) {
            if (ex instanceof Err)
                throw (Err) ex;
            else
                throw new ErrorFatal("Unknown exception occurred: " + ex, ex);
        }
    }

    /**
     * Based on the specified "options", execute one command and return the
     * resulting A4Solution object.
     * <p>
     * Note: it will first test whether the model fits one of the model from the
     * "Software Abstractions" book; if so, it will use the exact instance that was
     * in the book.
     *
     * @param rep - if nonnull, we'll send compilation diagnostic messages to it
     * @param sigs - the list of sigs; this list must be complete
     * @param cmd - the Command to execute
     * @param opt - the set of options guiding the execution of the command
     * @return null if the user chose "save to FILE" as the SAT solver, and nonnull
     *         if the solver finishes the entire solving and is either satisfiable
     *         or unsatisfiable.
     *         <p>
     *         If the return value X is satisfiable, you can call X.next() to get
     *         the next satisfying solution X2; and you can call X2.next() to get
     *         the next satisfying solution X3... until you get an unsatisfying
     *         solution.
     */
    public static A4Solution execute_commandFromBook(A4Reporter rep, Iterable<Sig> sigs, Command cmd, A4Options opt) throws Err {
        if (rep == null)
            rep = A4Reporter.NOP;
        TranslateAlloyToKodkod tr = null;
        try {
            if (cmd.parent != null || !cmd.getGrowableSigs().isEmpty())
                return execute_greedyCommand(rep, sigs, cmd, opt);
            tr = new TranslateAlloyToKodkod(rep, opt, sigs, cmd);
            tr.makeFacts(cmd.formula);
            return tr.frame.solve(rep, cmd, new Simplifier(), true);
        } catch (UnsatisfiedLinkError ex) {
            throw new ErrorFatal("The required JNI library cannot be found: " + ex.toString().trim(), ex);
        } catch (CapacityExceededException ex) {
            throw rethrow(ex);
        } catch (HigherOrderDeclException ex) {
            Pos p = tr != null ? tr.frame.kv2typepos(ex.decl().variable()).b : Pos.UNKNOWN;
            throw new ErrorType(p, "Analysis cannot be performed since it requires higher-order quantification that could not be skolemized.");
        } catch (Throwable ex) {
            if (ex instanceof Err)
                throw (Err) ex;
            else
                throw new ErrorFatal("Unknown exception occurred: " + ex, ex);
        }
    }

    /**
     * Translate the Alloy expression into an equivalent Kodkod Expression or
     * IntExpression or Formula object.
     *
     * @param sol - an existing satisfiable A4Solution object
     * @param expr - this is the Alloy expression we want to translate
     */
    public static Object alloy2kodkod(A4Solution sol, Expr expr) throws Err {
        if (expr.ambiguous && !expr.errors.isEmpty())
            expr = expr.resolve(expr.type(), null);
        if (!expr.errors.isEmpty())
            throw expr.errors.pick();
        TranslateAlloyToKodkod tr = new TranslateAlloyToKodkod(sol.getBitwidth(), sol.unrolls(), sol.a2k(), sol.s2k());
        Object ans;
        try {
            ans = tr.visitThis(expr);
        } catch (UnsatisfiedLinkError ex) {
            throw new ErrorFatal("The required JNI library cannot be found: " + ex.toString().trim());
        } catch (CapacityExceededException ex) {
            throw rethrow(ex);
        } catch (HigherOrderDeclException ex) {
            throw new ErrorType("Analysis cannot be performed since it requires higher-order quantification that could not be skolemized.");
        } catch (Throwable ex) {
            if (ex instanceof Err)
                throw (Err) ex;
            throw new ErrorFatal("Unknown exception occurred: " + ex, ex);
        }
        if ((ans instanceof IntExpression) || (ans instanceof Formula) || (ans instanceof Expression))
            return ans;
        throw new ErrorFatal("Unknown internal error encountered in the evaluator.");
    }

    // ==============================================================================================================//

    /**
     * Convenience method that evalutes x and casts the result to be a Kodkod
     * Formula.
     *
     * @return the formula - if x evaluates to a Formula
     * @throws ErrorFatal - if x does not evaluate to a Formula
     */
    private Formula cform(Expr x) throws Err {
        if (!x.errors.isEmpty())
            throw x.errors.pick();
        Object y = visitThis(x);
        if (y instanceof Formula)
            return (Formula) y;
        throw new ErrorFatal(x.span(), "This should have been a formula.\nInstead it is " + y);
    }

    /**
     * Convenience method that evalutes x and cast the result to be a Kodkod
     * IntExpression.
     *
     * @return the integer expression - if x evaluates to an IntExpression
     * @throws ErrorFatal - if x does not evaluate to an IntExpression
     */
    private IntExpression cint(Expr x) throws Err {
        if (!x.errors.isEmpty())
            throw x.errors.pick();
        return toInt(x, visitThis(x));
    }

    private IntExpression toInt(Expr x, Object y) throws Err, ErrorFatal {
        // simplify: if y is int[Int[sth]] then return sth
        if (y instanceof ExprToIntCast) {
            ExprToIntCast y2 = (ExprToIntCast) y;
            if (y2.expression() instanceof IntToExprCast)
                return ((IntToExprCast) y2.expression()).intExpr();
        }
        // simplify: if y is Int[sth], then return sth
        if (y instanceof IntToExprCast)
            return ((IntToExprCast) y).intExpr();
        if (y instanceof IntExpression)
            return (IntExpression) y;
        // [AM]: maybe this conversion should be removed
        if (y instanceof Expression)
            return ((Expression) y).sum();
        throw new ErrorFatal(x.span(), "This should have been an integer expression.\nInstead it is " + y);
    }

    /**
     * Convenience method that evaluаtes x and cast the result to be a Kodkod
     * Expression.
     *
     * @return the expression - if x evaluates to an Expression
     * @throws ErrorFatal - if x does not evaluate to an Expression
     */
    private Expression cset(Expr x) throws Err {
        if (!x.errors.isEmpty())
            throw x.errors.pick();
        return toSet(x, visitThis(x));
    }

    private Expression toSet(Expr x, Object y) throws Err, ErrorFatal {
        if (y instanceof Expression)
            return (Expression) y;
        if (y instanceof IntExpression)
            return ((IntExpression) y).toExpression();
        throw new ErrorFatal(x.span(), "This should have been a set or a relation.\nInstead it is " + y);
    }

    // ==============================================================================================================//

    /**
     * Given a variable name "name", prepend the current function name to form a
     * meaningful "skolem name". (Note: this function does NOT, and need NOT
     * guarantee that the name it generates is unique)
     */
    private String skolem(String name) {
        if (current_function.size() == 0) {
            if (cmd != null && cmd.label.length() > 0 && cmd.label.indexOf('$') < 0)
                return cmd.label + "_" + name;
            else
                return name;
        }
        Func last = current_function.get(current_function.size() - 1);
        String funcname = tail(last.label);
        if (funcname.indexOf('$') < 0)
            return funcname + "_" + name;
        else
            return name;
    }

    // ==============================================================================================================//

    /**
     * If x = SOMETHING->RELATION where SOMETHING.arity==1, then return the
     * RELATION, else return null.
     */
    private static Relation right(Expression x) {
        if (!(x instanceof BinaryExpression))
            return null;
        BinaryExpression bin = (BinaryExpression) x;
        if (bin.op() != ExprOperator.PRODUCT)
            return null;
        if (bin.left().arity() == 1 && bin.right() instanceof Relation)
            return (Relation) (bin.right());
        else
            return null;
    }

    // ==============================================================================================================//

    /* ============================ */
    /* Evaluates an ExprITE node. */
    /* ============================ */

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprITE x) throws Err {
        Formula c = cform(x.cond);
        Object l = visitThis(x.left);
        if (l instanceof Formula) {
            Formula c1 = c.implies((Formula) l);
            Formula c2 = c.not().implies(cform(x.right));
            return k2pos(c1.and(c2), x);
        }
        if (l instanceof Expression) {
            return c.thenElse((Expression) l, cset(x.right));
        }
        return c.thenElse((IntExpression) l, cint(x.right));
    }

    /* ============================ */
    /* Evaluates an ExprLet node. */
    /* ============================ */

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprLet x) throws Err {
        env.put(x.var, visitThis(x.expr));
        Object ans = visitThis(x.sub);
        env.remove(x.var);
        return ans;
    }

    /* ================================= */
    /* Evaluates an ExprConstant node. */
    /* ================================= */

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprConstant x) throws Err {
        switch (x.op) {
            case MIN :
                return IntConstant.constant(min); // TODO
            case MAX :
                return IntConstant.constant(max); // TODO
            case NEXT :
                return A4Solution.KK_NEXT;
            case TRUE :
                return Formula.TRUE;
            case FALSE :
                return Formula.FALSE;
            case EMPTYNESS :
                return Expression.NONE;
            case IDEN :
                return Expression.IDEN.intersection(a2k(UNIV).product(Expression.UNIV));
            case STRING :
                Expression ans = s2k(x.string);
                if (ans == null)
                    throw new ErrorFatal(x.pos, "String literal " + x + " does not exist in this instance.\n");
                return ans;
            case NUMBER :
                int n = x.num();
                // [am] const
                // if (n<min) throw new ErrorType(x.pos, "Current bitwidth is
                // set to "+bitwidth+", thus this integer constant "+n+" is
                // smaller than the minimum integer "+min);
                // if (n>max) throw new ErrorType(x.pos, "Current bitwidth is
                // set to "+bitwidth+", thus this integer constant "+n+" is
                // bigger than the maximum integer "+max);
                return IntConstant.constant(n).toExpression();
        }
        throw new ErrorFatal(x.pos, "Unsupported operator (" + x.op + ") encountered during ExprConstant.accept()");
    }

    /* ============================== */
    /* Evaluates an ExprUnary node. */
    /* ============================== */

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprUnary x) throws Err {
        switch (x.op) {
            case EXACTLYOF :
            case SOMEOF :
            case LONEOF :
            case ONEOF :
            case SETOF :
                return cset(x.sub);
            case NOOP :
                return visitThis(x.sub);
            case NOT :
                return k2pos(cform(x.sub).not(), x);
            case AFTER :
                return k2pos(cform(x.sub).after(), x);
            case ALWAYS :
                return k2pos(cform(x.sub).always(), x);
            case EVENTUALLY :
                return k2pos(cform(x.sub).eventually(), x);
            case BEFORE :
                return k2pos(cform(x.sub).before(), x);
            case HISTORICALLY :
                return k2pos(cform(x.sub).historically(), x);
            case ONCE :
                return k2pos(cform(x.sub).once(), x);
            case SOME :
                return k2pos(cset(x.sub).some(), x);
            case LONE :
                return k2pos(cset(x.sub).lone(), x);
            case ONE :
                return k2pos(cset(x.sub).one(), x);
            case NO :
                return k2pos(cset(x.sub).no(), x);
            case PRIME :
                return cset(x.sub).prime();
            case TRANSPOSE :
                return cset(x.sub).transpose();
            case CARDINALITY :
                return cset(x.sub).count();
            case CAST2SIGINT :
                return cint(x.sub).toExpression();
            case CAST2INT :
                return sum(cset(x.sub));
            case RCLOSURE :
                Expression iden = Expression.IDEN.intersection(a2k(UNIV).product(Expression.UNIV));
                return cset(x.sub).closure().union(iden);
            case CLOSURE :
                return cset(x.sub).closure();
        }
        throw new ErrorFatal(x.pos, "Unsupported operator (" + x.op + ") encountered during ExprUnary.visit()");
    }

    /**
     * Performs int[x]; contains an efficiency shortcut that simplifies int[Int[x]]
     * to x.
     */
    private IntExpression sum(Expression x) {
        if (x instanceof IntToExprCast)
            return ((IntToExprCast) x).intExpr();
        else
            return x.sum();
    }

    /* ============================ */
    /* Evaluates an ExprVar node. */
    /* ============================ */

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprVar x) throws Err {
        Object ans = env.get(x);
        if (ans == null)
            ans = a2k(x);
        if (ans == null)
            throw new ErrorFatal(x.pos, "Variable \"" + x + "\" is not bound to a legal value during translation.\n");
        return ans;
    }

    /* ========================= */
    /* Evaluates a Field node. */
    /* ========================= */

    /** {@inheritDoc} */
    @Override
    public Object visit(Field x) throws Err {
        Expression ans = a2k(x);
        if (ans == null)
            throw new ErrorFatal(x.pos, "Field \"" + x + "\" is not bound to a legal value during translation.\n");
        return ans;
    }

    /* ======================= */
    /* Evaluates a Sig node. */
    /* ======================= */

    /** {@inheritDoc} */
    @Override
    public Object visit(Sig x) throws Err {
        Expression ans = a2k(x);
        if (ans == null)
            throw new ErrorFatal(x.pos, "Sig \"" + x + "\" is not bound to a legal value during translation.\n");
        return ans;
    }

    /* ============================= */
    /* Evaluates an ExprCall node. */
    /* ============================= */

    /**
     * Caches parameter-less functions to a Kodkod Expression, Kodkod IntExpression,
     * or Kodkod Formula.
     */
    private final Map<Func,Object> cacheForConstants = new IdentityHashMap<Func,Object>();

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprCall x) throws Err {
        final Func f = x.fun;
        final Object candidate = f.count() == 0 ? cacheForConstants.get(f) : null;
        if (candidate != null)
            return candidate;
        final Expr body = f.getBody();
        if (body.type().arity() < 0 || body.type().arity() != f.returnDecl.type().arity())
            throw new ErrorType(body.span(), "Function return value not fully resolved.");
        final int n = f.count();
        int maxRecursion = unrolls;
        for (Func ff : current_function)
            if (ff == f) {
                if (maxRecursion < 0) {
                    throw new ErrorSyntax(x.span(), "" + f + " cannot call itself recursively!");
                }
                if (maxRecursion == 0) {
                    Type t = f.returnDecl.type();
                    if (t.is_bool)
                        return Formula.FALSE;
                    if (t.is_int())
                        return IntConstant.constant(0);
                    int i = t.arity();
                    Expression ans = Expression.NONE;
                    while (i > 1) {
                        ans = ans.product(Expression.NONE);
                        i--;
                    }
                    return ans;
                }
                maxRecursion--;
            }
        Env<ExprVar,Object> newenv = new Env<ExprVar,Object>();
        for (int i = 0; i < n; i++)
            newenv.put(f.get(i), cset(x.args.get(i)));
        Env<ExprVar,Object> oldenv = env;
        env = newenv;
        current_function.add(f);
        Object ans = visitThis(body);
        env = oldenv;
        current_function.remove(current_function.size() - 1);
        if (ans instanceof Formula)
            k2pos((Formula) ans, x);
        if (f.count() == 0)
            cacheForConstants.put(f, ans);
        return ans;
    }

    /* ================================ */
    /* Evaluates an ExprList node. */
    /* ================================ */

    /**
     * Helper method that merge a list of conjuncts or disjoints while minimizing
     * the AST depth (external caller should use i==1)
     */
    private Formula getSingleFormula(boolean isConjunct, int i, List<Expr> formulas) throws Err {
        // We actually build a "binary heap" where node X's two children are
        // node 2X and node 2X+1
        int n = formulas.size();
        if (n == 0)
            return isConjunct ? Formula.TRUE : Formula.FALSE;
        Formula me = cform(formulas.get(i - 1)), other;
        int child1 = i + i, child2 = child1 + 1;
        if (child1 < i || child1 > n)
            return me;
        other = getSingleFormula(isConjunct, child1, formulas);
        if (isConjunct)
            me = me.and(other);
        else
            me = me.or(other);
        if (child2 < 1 || child2 > n)
            return me;
        other = getSingleFormula(isConjunct, child2, formulas);
        if (isConjunct)
            me = me.and(other);
        else
            me = me.or(other);
        return me;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprList x) throws Err {
        if (x.op == ExprList.Op.AND || x.op == ExprList.Op.OR) {
            if (x.args.size() == 0)
                return (x.op == ExprList.Op.AND) ? Formula.TRUE : Formula.FALSE;
            Formula answer = getSingleFormula(x.op == ExprList.Op.AND, 1, x.args);
            return k2pos(answer, x);
        }
        if (x.op == ExprList.Op.TOTALORDER) {
            Expression elem = cset(x.args.get(0)), first = cset(x.args.get(1)), next = cset(x.args.get(2));
            if (elem instanceof Relation && first instanceof Relation && next instanceof Relation) {
                Relation lst = frame.addRel(((Relation) elem).name() + "_last", null, frame.query(true, elem, false), false); // [electrum] no unnamed rels for electrod
                totalOrderPredicates.add((Relation) elem);
                totalOrderPredicates.add((Relation) first);
                totalOrderPredicates.add(lst);
                totalOrderPredicates.add((Relation) next);
                return k2pos(((Relation) next).totalOrder((Relation) elem, (Relation) first, lst), x);
            }
            Formula f1 = elem.in(first.join(next.reflexiveClosure())); // every
                                                                      // element
                                                                      // is in
                                                                      // the
                                                                      // total
                                                                      // order
            Formula f2 = next.join(first).no(); // first element has no
                                               // predecessor
            Variable e = Variable.unary("v" + Integer.toString(cnt++));
            Formula f3 = e.eq(first).or(next.join(e).one()); // each element
                                                            // (except the
                                                            // first) has
                                                            // one
                                                            // predecessor
            Formula f4 = e.eq(elem.difference(next.join(elem))).or(e.join(next).one()); // each
                                                                                       // element
                                                                                       // (except
                                                                                       // the
                                                                                       // last)
                                                                                       // has
                                                                                       // one
                                                                                       // successor
            Formula f5 = e.in(e.join(next.closure())).not(); // there are no
                                                            // cycles
            return k2pos(f3.and(f4).and(f5).forAll(e.oneOf(elem)).and(f1).and(f2), x);
        }
        // This says no(a&b) and no((a+b)&c) and no((a+b+c)&d)...
        // Empirically this seems to be more efficient than "no(a&b) and no(a&c)
        // and no(b&c)"
        Formula answer = null;
        Expression a = null;
        for (Expr arg : x.args) {
            Expression b = cset(arg);
            if (a == null) {
                a = b;
                continue;
            }
            if (answer == null)
                answer = a.intersection(b).no();
            else
                answer = a.intersection(b).no().and(answer);
            a = a.union(b);
        }
        if (answer != null)
            return k2pos(answer, x);
        else
            return Formula.TRUE;
    }

    /* =============================== */
    /* Evaluates an ExprBinary node. */
    /* =============================== */

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprBinary x) throws Err {
        Expr a = x.left, b = x.right;
        Expression s, s2, eL, eR;
        IntExpression i;
        Formula f;
        Object objL, objR;
        switch (x.op) {
            // [electrum] changed from !a || b, was it relevant?
            case IMPLIES :
                f = cform(a).implies(cform(b));
                return k2pos(f, x);
            case IN :
                return k2pos(isIn(cset(a), b), x);
            case NOT_IN :
                return k2pos(isIn(cset(a), b).not(), x);
            case LT :
                i = cint(a);
                f = i.lt(cint(b));
                return k2pos(f, x);
            case LTE :
                i = cint(a);
                f = i.lte(cint(b));
                return k2pos(f, x);
            case GT :
                i = cint(a);
                f = i.gt(cint(b));
                return k2pos(f, x);
            case GTE :
                i = cint(a);
                f = i.gte(cint(b));
                return k2pos(f, x);
            case NOT_LT :
                i = cint(a);
                f = i.lt(cint(b)).not();
                return k2pos(f, x);
            case NOT_LTE :
                i = cint(a);
                f = i.lte(cint(b)).not();
                return k2pos(f, x);
            case NOT_GT :
                i = cint(a);
                f = i.gt(cint(b)).not();
                return k2pos(f, x);
            case NOT_GTE :
                i = cint(a);
                f = i.gte(cint(b)).not();
                return k2pos(f, x);
            case AND :
                f = cform(a);
                f = f.and(cform(b));
                return k2pos(f, x);
            case OR :
                f = cform(a);
                f = f.or(cform(b));
                return k2pos(f, x);
            case UNTIL :
                f = cform(a);
                f = f.until(cform(b));
                return k2pos(f, x);
            case RELEASES :
                f = cform(a);
                f = f.releases(cform(b));
                return k2pos(f, x);
            case SINCE :
                f = cform(a);
                f = f.since(cform(b));
                return k2pos(f, x);
            case TRIGGERED :
                f = cform(a);
                f = f.triggered(cform(b));
                return k2pos(f, x);
            case IFF :
                f = cform(a);
                f = f.iff(cform(b));
                return k2pos(f, x);
            case PLUSPLUS :
                s = cset(a);
                return s.override(cset(b));
            case MUL :
                i = cint(a);
                return i.multiply(cint(b));
            case DIV :
                i = cint(a);
                return i.divide(cint(b));
            case REM :
                i = cint(a);
                return i.modulo(cint(b));
            case SHL :
                i = cint(a);
                return i.shl(cint(b));
            case SHR :
                i = cint(a);
                return i.shr(cint(b));
            case SHA :
                i = cint(a);
                return i.sha(cint(b));
            case PLUS :
                return cset(a).union(cset(b));
            // [AM]
            // obj = visitThis(a);
            // if (obj instanceof IntExpression) { i=(IntExpression)obj; return
            // i.plus(cint(b)); }
            // s = (Expression)obj; return s.union(cset(b));
            case IPLUS :
                return cint(a).plus(cint(b));
            case MINUS :
                // Special exception to allow "0-8" to not throw an exception,
                // where 7 is the maximum allowed integer (when bitwidth==4)
                // (likewise, when bitwidth==5, then +15 is the maximum allowed
                // integer, and we want to allow 0-16 without throwing an
                // exception)
                if (a instanceof ExprConstant && ((ExprConstant) a).op == ExprConstant.Op.NUMBER && ((ExprConstant) a).num() == 0)
                    if (b instanceof ExprConstant && ((ExprConstant) b).op == ExprConstant.Op.NUMBER && ((ExprConstant) b).num() == max + 1)
                        return IntConstant.constant(min);
                return cset(a).difference(cset(b));
            // [AM]
            // obj=visitThis(a);
            // if (obj instanceof IntExpression) { i=(IntExpression)obj; return
            // i.minus(cint(b));}
            // s=(Expression)obj; return s.difference(cset(b));
            case IMINUS :
                return cint(a).minus(cint(b));
            case INTERSECT :
                s = cset(a);
                return s.intersection(cset(b));
            case ANY_ARROW_SOME :
            case ANY_ARROW_ONE :
            case ANY_ARROW_LONE :
            case SOME_ARROW_ANY :
            case SOME_ARROW_SOME :
            case SOME_ARROW_ONE :
            case SOME_ARROW_LONE :
            case ONE_ARROW_ANY :
            case ONE_ARROW_SOME :
            case ONE_ARROW_ONE :
            case ONE_ARROW_LONE :
            case LONE_ARROW_ANY :
            case LONE_ARROW_SOME :
            case LONE_ARROW_ONE :
            case LONE_ARROW_LONE :
            case ISSEQ_ARROW_LONE :
            case ARROW :
                s = cset(a);
                return s.product(cset(b));
            case JOIN :
                a = a.deNOP();
                s = cset(a);
                s2 = cset(b);
                if (a instanceof Sig && ((Sig) a).isOne != null && s2 instanceof BinaryExpression) {
                    BinaryExpression bin = (BinaryExpression) s2;
                    if (bin.op() == ExprOperator.PRODUCT && bin.left() == s)
                        return bin.right();
                }
                return s.join(s2);
            case EQUALS :
                objL = visitThis(a);
                objR = visitThis(b);
                eL = toSet(a, objL);
                eR = toSet(b, objR);
                if (eL instanceof IntToExprCast && eR instanceof IntToExprCast)
                    f = ((IntToExprCast) eL).intExpr().eq(((IntToExprCast) eR).intExpr());
                else
                    f = eL.eq(eR);
                return k2pos(f, x);
            case NOT_EQUALS :
                objL = visitThis(a);
                objR = visitThis(b);
                eL = toSet(a, objL);
                eR = toSet(b, objR);
                if (eL instanceof IntToExprCast && eR instanceof IntToExprCast)
                    f = ((IntToExprCast) eL).intExpr().eq(((IntToExprCast) eR).intExpr()).not();
                else
                    f = eL.eq(eR).not();
                return k2pos(f, x);
            case DOMAIN :
                s = cset(a);
                s2 = cset(b);
                for (int j = s2.arity(); j > 1; j--)
                    s = s.product(Expression.UNIV);
                return s.intersection(s2);
            case RANGE :
                s = cset(a);
                s2 = cset(b);
                for (int j = s.arity(); j > 1; j--)
                    s2 = Expression.UNIV.product(s2);
                return s.intersection(s2);
        }
        throw new ErrorFatal(x.pos, "Unsupported operator (" + x.op + ") encountered during ExprBinary.accept()");
    }

    /**
     * Helper method that translates the formula "a in b" into a Kodkod formula.
     */
    private Formula isIn(Expression a, Expr right) throws Err {
        Expression b;
        if (right instanceof ExprBinary && right.mult != 0 && ((ExprBinary) right).op.isArrow) {
            // Handles possible "binary" or higher-arity multiplicity
            return isInBinary(a, (ExprBinary) right);
        }
        switch (right.mult()) {
            case EXACTLYOF :
                b = cset(right);
                return a.eq(b);
            case ONEOF :
                b = cset(right);
                return a.one().and(a.in(b));
            case LONEOF :
                b = cset(right);
                return a.lone().and(a.in(b));
            case SOMEOF :
                b = cset(right);
                return a.some().and(a.in(b));
            default :
                b = cset(right);
                return a.in(b);
        }
    }

    // [AM]
    private static boolean am = true;

    /**
     * Helper method that translates the formula "r in (a ?->? b)" into a Kodkod
     * formula.
     */
    private Formula isInBinary(Expression r, ExprBinary ab) throws Err {
        final Expression a = cset(ab.left), b = cset(ab.right);
        Decls d = null, d2 = null;
        Formula ans1, ans2;
        // "R in A ->op B" means for each tuple a in A, there are "op" tuples in
        // r that begins with a.
        Expression atuple = null, ar = r;
        for (int i = a.arity(); i > 0; i--) {
            Variable v = Variable.unary("v" + Integer.toString(cnt++));
            if (!am) {
                if (a.arity() == 1)
                    d = v.oneOf(a);
                else if (d == null)
                    d = v.oneOf(Expression.UNIV);
                else
                    d = v.oneOf(Expression.UNIV).and(d);
            } else {
                d = am(a, d, i, v);
            }
            ar = v.join(ar);
            if (atuple == null)
                atuple = v;
            else
                atuple = atuple.product(v);
        }
        ans1 = isIn(ar, ab.right);
        switch (ab.op) {
            case ISSEQ_ARROW_LONE :
            case ANY_ARROW_LONE :
            case SOME_ARROW_LONE :
            case ONE_ARROW_LONE :
            case LONE_ARROW_LONE :
                ans1 = ar.lone().and(ans1);
                break;
            case ANY_ARROW_ONE :
            case SOME_ARROW_ONE :
            case ONE_ARROW_ONE :
            case LONE_ARROW_ONE :
                ans1 = ar.one().and(ans1);
                break;
            case ANY_ARROW_SOME :
            case SOME_ARROW_SOME :
            case ONE_ARROW_SOME :
            case LONE_ARROW_SOME :
                ans1 = ar.some().and(ans1);
                break;
        }
        if (a.arity() > 1) {
            Formula tmp = isIn(atuple, ab.left);
            if (tmp != Formula.TRUE)
                ans1 = tmp.implies(ans1);
        }
        ans1 = ans1.forAll(d);
        // "R in A op-> B" means for each tuple b in B, there are "op" tuples in
        // r that end with b.
        Expression btuple = null, rb = r;
        for (int i = b.arity(); i > 0; i--) {
            Variable v = Variable.unary("v" + Integer.toString(cnt++));
            if (!am) {
                if (b.arity() == 1)
                    d2 = v.oneOf(b);
                else if (d2 == null)
                    d2 = v.oneOf(Expression.UNIV);
                else
                    d2 = v.oneOf(Expression.UNIV).and(d2);
            } else {
                d2 = am(b, d2, i, v);
            }
            rb = rb.join(v);
            if (btuple == null)
                btuple = v;
            else
                btuple = v.product(btuple);
        }
        ans2 = isIn(rb, ab.left);
        switch (ab.op) {
            case LONE_ARROW_ANY :
            case LONE_ARROW_SOME :
            case LONE_ARROW_ONE :
            case LONE_ARROW_LONE :
                ans2 = rb.lone().and(ans2);
                break;
            case ONE_ARROW_ANY :
            case ONE_ARROW_SOME :
            case ONE_ARROW_ONE :
            case ONE_ARROW_LONE :
                ans2 = rb.one().and(ans2);
                break;
            case SOME_ARROW_ANY :
            case SOME_ARROW_SOME :
            case SOME_ARROW_ONE :
            case SOME_ARROW_LONE :
                ans2 = rb.some().and(ans2);
                break;
        }
        if (b.arity() > 1) {
            Formula tmp = isIn(btuple, ab.right);
            if (tmp != Formula.TRUE)
                ans2 = tmp.implies(ans2);
        }
        ans2 = ans2.forAll(d2);
        // Now, put everything together
        Formula ans = r.in(a.product(b)).and(ans1).and(ans2);
        if (ab.op == ExprBinary.Op.ISSEQ_ARROW_LONE) {
            Expression rr = r;
            while (rr.arity() > 1)
                rr = rr.join(Expression.UNIV);
            ans = rr.difference(rr.join(A4Solution.KK_NEXT)).in(A4Solution.KK_ZERO).and(ans);
        }
        return ans;
    }

    private Decls am(final Expression a, Decls d, int i, Variable v) {
        Expression colType;
        if (a.arity() == 1) {
            assert i == 1;
            colType = a;
        } else {
            // colType = a.project(IntConstant.constant(i - 1))); //UNSOUND
            colType = Expression.UNIV;
        }
        return (d == null) ? v.oneOf(colType) : d.and(v.oneOf(colType));
    }

    /* =========================== */
    /* Evaluates an ExprQt node. */
    /* =========================== */

    /**
     * Adds a "one of" in front of X if X is unary and does not have a declared
     * multiplicity.
     */
    private static Expr addOne(Expr x) {
        Expr save = x;
        while (x instanceof ExprUnary) {
            switch (((ExprUnary) x).op) {
                case EXACTLYOF :
                case SETOF :
                case ONEOF :
                case LONEOF :
                case SOMEOF :
                    return save;
                case NOOP :
                    x = ((ExprUnary) x).sub;
                    continue;
                default :
                    break;
            }
        }
        return (x.type().arity() != 1) ? x : ExprUnary.Op.ONEOF.make(x.span(), x);
    }

    /**
     * Helper method that translates the quantification expression "op vars | sub"
     */
    private Object visit_qt(final ExprQt.Op op, final ConstList<Decl> xvars, final Expr sub) throws Err {
        if (op == ExprQt.Op.NO) {
            return visit_qt(ExprQt.Op.ALL, xvars, sub.not());
        }
        if (op == ExprQt.Op.ONE || op == ExprQt.Op.LONE) {
            boolean ok = true;
            for (int i = 0; i < xvars.size(); i++) {
                Expr v = addOne(xvars.get(i).expr).deNOP();
                if (v.type().arity() != 1 || v.mult() != ExprUnary.Op.ONEOF) {
                    ok = false;
                    break;
                }
            }
            if (op == ExprQt.Op.ONE && ok)
                return ((Expression) visit_qt(ExprQt.Op.COMPREHENSION, xvars, sub)).one();
            if (op == ExprQt.Op.LONE && ok)
                return ((Expression) visit_qt(ExprQt.Op.COMPREHENSION, xvars, sub)).lone();
        }
        if (op == ExprQt.Op.ONE) {
            Formula f1 = (Formula) visit_qt(ExprQt.Op.LONE, xvars, sub);
            Formula f2 = (Formula) visit_qt(ExprQt.Op.SOME, xvars, sub);
            return f1.and(f2);
        }
        if (op == ExprQt.Op.LONE) {
            QuantifiedFormula p1 = (QuantifiedFormula) visit_qt(ExprQt.Op.ALL, xvars, sub);
            QuantifiedFormula p2 = (QuantifiedFormula) visit_qt(ExprQt.Op.ALL, xvars, sub);
            Decls s1 = p1.decls(), s2 = p2.decls(), decls = null;
            Formula f1 = p1.formula(), f2 = p2.formula();
            Formula[] conjuncts = new Formula[s1.size()];
            for (int i = 0; i < conjuncts.length; i++) {
                kodkod.ast.Decl d1 = s1.get(i), d2 = s2.get(i);
                conjuncts[i] = d1.variable().eq(d2.variable());
                if (decls == null)
                    decls = d1.and(d2);
                else
                    decls = decls.and(d1).and(d2);
            }
            return f1.and(f2).implies(Formula.and(conjuncts)).forAll(decls);
        }
        Decls dd = null;
        List<Formula> guards = new ArrayList<Formula>();
        for (Decl dep : xvars) {
            final Expr dexexpr = addOne(dep.expr);
            final Expression dv = cset(dexexpr);
            for (ExprHasName dex : dep.names) {
                final Variable v = Variable.nary(skolem(dex.label), dex.type().arity());
                final kodkod.ast.Decl newd;
                env.put((ExprVar) dex, v);
                if (dex.type().arity() != 1) {
                    guards.add(isIn(v, dexexpr));
                    newd = v.setOf(dv);
                } else
                    switch (dexexpr.mult()) {
                        case SETOF :
                            newd = v.setOf(dv);
                            break;
                        case SOMEOF :
                            newd = v.someOf(dv);
                            break;
                        case LONEOF :
                            newd = v.loneOf(dv);
                            break;
                        default :
                            newd = v.oneOf(dv);
                    }
                if (frame != null)
                    frame.kv2typepos(v, dex.type(), dex.pos);
                if (dd == null)
                    dd = newd;
                else
                    dd = dd.and(newd);
            }
        }
        final Formula ans = (op == ExprQt.Op.SUM) ? null : cform(sub);
        final IntExpression ians = (op != ExprQt.Op.SUM) ? null : cint(sub);
        for (Decl d : xvars)
            for (ExprHasName v : d.names)
                env.remove((ExprVar) v);
        if (op == ExprQt.Op.COMPREHENSION)
            return ans.comprehension(dd); // guards.size()==0, since each var
                                         // has to be unary
        if (op == ExprQt.Op.SUM)
            return ians.sum(dd); // guards.size()==0, since each var has to be
                                // unary
        if (op == ExprQt.Op.SOME) {
            if (guards.size() == 0)
                return ans.forSome(dd);
            guards.add(ans);
            return Formula.and(guards).forSome(dd);
        } else {
            if (guards.size() == 0)
                return ans.forAll(dd);
            return Formula.and(guards).implies(ans).forAll(dd);
        }
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprQt x) throws Err {
        Expr xx = x.desugar();
        if (xx instanceof ExprQt)
            x = (ExprQt) xx;
        else
            return visitThis(xx);
        Object ans = visit_qt(x.op, x.decls, x.sub);
        if (ans instanceof Formula)
            k2pos((Formula) ans, x);
        return ans;
    }
}
