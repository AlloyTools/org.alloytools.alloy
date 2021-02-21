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

package edu.mit.csail.sdg.parser;

import static edu.mit.csail.sdg.alloy4.Util.asList;
import static edu.mit.csail.sdg.ast.Attr.AttrType.ABSTRACT;
import static edu.mit.csail.sdg.ast.Attr.AttrType.ONE;
import static edu.mit.csail.sdg.ast.Attr.AttrType.PRIVATE;
import static edu.mit.csail.sdg.ast.Attr.AttrType.SUBSET;
import static edu.mit.csail.sdg.ast.Attr.AttrType.SUBSIG;
import static edu.mit.csail.sdg.ast.Attr.AttrType.WHERE;
import static edu.mit.csail.sdg.ast.Sig.NONE;
import static edu.mit.csail.sdg.ast.Sig.SEQIDX;
import static edu.mit.csail.sdg.ast.Sig.SIGINT;
import static edu.mit.csail.sdg.ast.Sig.STRING;
import static edu.mit.csail.sdg.ast.Sig.UNIV;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ConstList.TempList;
import edu.mit.csail.sdg.alloy4.Env;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.JoinableList;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4.Version;
import edu.mit.csail.sdg.ast.Attr;
import edu.mit.csail.sdg.ast.Browsable;
import edu.mit.csail.sdg.ast.Clause;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.CommandScope;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBad;
import edu.mit.csail.sdg.ast.ExprBadCall;
import edu.mit.csail.sdg.ast.ExprBadJoin;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprChoice;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.ModuleReference;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Sig.PrimSig;
import edu.mit.csail.sdg.ast.Sig.SubsetSig;
import edu.mit.csail.sdg.ast.Type;
import edu.mit.csail.sdg.ast.VisitQuery;
import edu.mit.csail.sdg.ast.VisitQueryOnce;
import edu.mit.csail.sdg.ast.VisitReturn;

/**
 * Mutable; this class represents an Alloy module; equals() uses object
 * identity.
 *
 * @modified [electrum] adapted methods to support commands with trace prefix
 *           length scopes; added the detection of errors and warnings during
 *           signature/field/command resolution; note that up Alloy5 signature
 *           resolution did not throw warnings since those arose only from type
 *           system warnings
 *
 *           the following warnings are thrown: if a static sig is in a variable
 *           sig (since this makes part of the parent immutable); if a static
 *           sig extends a variable sig (since this makes part of the parent
 *           immutable); if a variable sig extends a static sig (redundant since
 *           it will be immutable anyway); if a static field is declared in a
 *           variable sig (since this makes part of the sig immutable); if a
 *           static field is declared with a variable bounding expression (since
 *           this makes part bounding expression immutable)
 *
 *           the following errors are thrown: if scopes are assigned to
 *           non-top-level variable sigs; if exact scopes are assigned to
 *           variable sigs; if a module declares a parameter as exact and a
 *           variable argument is passed
 */

public final class CompModule extends Browsable implements Module {

    // These fields are shared by all Modules that point to each other

    /**
     * Maps each actual Sig to the original parser-generated Sig that it came from.
     */
    private final LinkedHashMap<Sig,Sig>        new2old;

    /**
     * Maps each parser-generated Sig to its original list of field declarations.
     */
    private final LinkedHashMap<Sig,List<Decl>> old2fields;

    /**
     * Maps each parser-generated Sig to its original appended facts.
     */
    private final LinkedHashMap<Sig,Expr>       old2appendedfacts;

    /** Maps each Sig to the CompModule it belongs to. */
    private final HashMap<Sig,CompModule>       sig2module;

    /** The list of CompModules. */
    private final List<CompModule>              allModules;

    /**
     * The list of sigs in the entire world whose scope shall be deemed "exact"
     */
    private final Set<Sig>                      exactSigs;

    /**
     * This stores a set of global values; given a unresolved name, we query this
     * map first before all else.
     */
    private final Map<String,Expr>              globals;

    /** This stores the meta signature "sig$" */
    private final PrimSig                       metaSig;

    /** This stores the meta signature "field$" */
    private final PrimSig                       metaField;

    // ============================================================================================================================//

    /**
     * This field is used during a depth-first search of the dag-of-module(s) to
     * mark which modules have been visited.
     */
    private Object                              visitedBy = null;

    /** The world that this CompModule belongs to. */
    private final CompModule                    world;

    /**
     * The simplest path pointing to this Module ("" if this is the main module)
     */
    public final String                         path;

    /**
     * Return the simplest path pointing to this Module ("" if this is the main
     * module)
     */
    @Override
    public String path() {
        return path;
    }

    /**
     * 1: has seen the "module" line 3: has seen the
     * "sig/pred/fun/fact/assert/check/run" commands
     */
    private int                   status     = 0;

    /**
     * The position of the "MODULE" line at the top of the file; Pos.UNKNOWN if the
     * line has not been parsed from the file yet.
     */
    private Pos                   modulePos  = Pos.UNKNOWN;

    /**
     * The text of the "MODULE" line at the top of the file; "unknown" if the line
     * has not be parsed from the file yet.
     */
    private String                moduleName = "unknown";

    /**
     * Whether we have seen a name containing a dollar sign or not.
     */
    boolean                       seenDollar = false;

    /**
     * Each param is mapped to its corresponding Sig (or null if we have not
     * resolved it).
     */
    private final Map<String,Sig> params     = new LinkedHashMap<String,Sig>();				// Must
    // be
    // LinkedHashMap
    // since
    // the
    // order
    // matters

    /**
     * Each alias is mapped to its corresponding "open" statement.
     */
    private final Map<String,Open>            opens       = new LinkedHashMap<String,Open>();

    /** Each sig name is mapped to its corresponding SigAST. */
    private final Map<String,Sig>             sigs        = new LinkedHashMap<String,Sig>();

    /**
     * The list of params in this module whose scope shall be deemed "exact"
     */
    private final List<String>                exactParams = new ArrayList<String>();

    /**
     * The current name resolution mode (0=pure) (1=Alloy 4.1.3 and older) (2=new)
     */
    int                                       resolution  = 1;

    /**
     * Each func name is mapped to a nonempty list of FunAST objects.
     */
    private final Map<String,ArrayList<Func>> funcs       = new LinkedHashMap<String,ArrayList<Func>>();

    /** Each macro name is mapped to a MacroAST object. */
    private final Map<String,Macro>           macros      = new LinkedHashMap<String,Macro>();

    /** Each assertion name is mapped to its Expr. */
    private final Map<String,Expr>            asserts     = new LinkedHashMap<String,Expr>();

    /**
     * The list of facts; each fact is either an untypechecked Exp or a typechecked
     * Expr.
     */
    private final List<Pair<String,Expr>>     facts       = new ArrayList<Pair<String,Expr>>();

    /**
     * The list of (CommandName,Command,Expr) triples; NOTE: duplicate command names
     * are allowed.
     */
    private final List<Command>               commands    = new ArrayList<Command>();

    // ============================================================================================================================//

    /**
     * Mutable; this class represents the current typechecking context.
     */
    static final class Context extends VisitReturn<Expr> {

        /**
         * The place where warnings should go; can be null if we don't care about
         * storing the warnings.
         */
        private List<ErrorWarning>     warns;

        /** The module that the current context is in. */
        final CompModule               rootmodule;

        /**
         * Nonnull if we are typechecking a field declaration or a sig appended facts.
         */
        Sig                            rootsig      = null;

        /** Nonnull if we are typechecking a field declaration. */
        private Decl                   rootfield    = null;

        /**
         * True if we are typechecking a function's parameter declarations or return
         * declaration.
         */
        private boolean                rootfunparam = false;

        /** Nonnull if we are typechecking a function's body. */
        private Func                   rootfunbody  = null;

        /**
         * This maps local names (eg. let/quantification variables and function
         * parameters) to the objects they refer to.
         */
        private final Env<String,Expr> env          = new Env<String,Expr>();

        /** The level of macro substitution recursion. */
        public final int               unrolls;

        public final boolean           isIntsNotUsed;

        /**
         * Associates the given name with the given expression in the current lexical
         * scope.
         */
        final void put(String name, Expr value) {
            env.put(name, value);
        }

        /**
         * Removes the latest binding for the given name from the current lexical scope.
         */
        final void remove(String name) {
            env.remove(name);
        }

        /** Construct a new Context with an empty lexical scope. */
        Context(CompModule rootModule, List<ErrorWarning> warns) {
            this(rootModule, warns, 20); // 20 is a reasonable threshold; deeper
                                        // than this would likely be too big
                                        // to solve anyway
        }

        /** Construct a new Context with an empty lexical scope. */
        Context(CompModule rootModule, List<ErrorWarning> warns, int unrolls) {
            this.rootmodule = rootModule;
            this.unrolls = unrolls;
            this.warns = warns;
            boolean noIntFields = !CompUtil.areIntsUsed(rootModule.getAllReachableSigs(), null);
            boolean noOpenInteger = true;
            for (Open o : rootModule.opens.values()) {
                if (("util/integer".equals(o.filename) || "util\\integer".equals(o.filename)) && o.pos != null) {
                    noOpenInteger = false;
                    break;
                }
            }
            this.isIntsNotUsed = false; // TODO InoIntFields && noOpenInteger;
        }

        /**
         * Resolve the given name to get a collection of Expr and Func objects.
         */
        public Expr resolve(final Pos pos, final String name) {
            if (name.indexOf('/') >= 0) {
                String n = name.startsWith("this/") ? name.substring(5) : name;
                CompModule mod = rootmodule;
                while (true) {
                    int i = n.indexOf('/');
                    if (i < 0) {
                        Macro m = mod.macros.get(n);
                        if (m == null || (m.isPrivate != null && mod != rootmodule))
                            break;
                        else
                            return m.changePos(pos);
                    }
                    String alias = n.substring(0, i);
                    Open uu = mod.opens.get(alias);
                    if (uu == null || uu.realModule == null || uu.isPrivate)
                        break;
                    n = n.substring(i + 1);
                    mod = uu.realModule;
                }
            }
            Expr match = env.get(name);
            if (match == null) {
                boolean ambiguous = false;
                StringBuilder sb = new StringBuilder();
                for (CompModule m : rootmodule.getAllNameableModules()) {
                    Macro mac = m.macros.get(name);
                    if (mac == null)
                        continue;
                    if (match != null)
                        ambiguous = true;
                    else
                        match = mac;
                    sb.append("\n").append(m.path.length() == 0 ? "this" : m.path).append("/").append(name);
                }
                if (ambiguous)
                    return new ExprBad(pos, name, new ErrorType(pos, "There are multiple macros with the same name:" + sb));
            }
            if (match == null)
                match = rootmodule.globals.get(name);
            if (match != null) {
                if (match instanceof Macro)
                    return ((Macro) match).changePos(pos);
                match = ExprUnary.Op.NOOP.make(pos, match);
                return ExprChoice.make(isIntsNotUsed, pos, asList(match), asList(name));
            }
            Expr th = env.get("this");
            if (th != null)
                th = ExprUnary.Op.NOOP.make(pos, th);
            TempList<Expr> ch = new TempList<Expr>();
            TempList<String> re = new TempList<String>();
            Expr ans = rootmodule.populate(ch, re, rootfield, rootsig, rootfunparam, rootfunbody, pos, name, th);
            if (ans != null)
                return ans;
            if (ch.size() == 0)
                return new ExprBad(pos, name, hint(pos, name));
            else
                return ExprChoice.make(isIntsNotUsed, pos, ch.makeConst(), re.makeConst());
        }

        Expr check(Expr x) throws Err {
            return visitThis(x);
        }

        /**
         * Returns true if the function's parameters have reasonable intersection with
         * the list of arguments. <br>
         * If args.length() > f.params.size(), the extra arguments are ignored by this
         * check
         */
        private static boolean applicable(Func f, List<Expr> args) {
            if (f.count() > args.size())
                return false;
            int i = 0;
            for (ExprVar d : f.params()) {
                Type param = d.type(), arg = args.get(i).type();
                i++;
                // The reason we don't directly compare "arg.arity()" with
                // "param.arity()"
                // is because the arguments may not be fully resolved yet.
                if (!arg.hasCommonArity(param))
                    return false;
                if (arg.hasTuple() && param.hasTuple() && !arg.intersects(param))
                    return false;
            }
            return true;
        }

        private Expr process(Pos pos, Pos closingBracket, Pos rightPos, List<Expr> choices, List<String> oldReasons, Expr arg) {
            TempList<Expr> list = new TempList<Expr>(choices.size());
            TempList<String> reasons = new TempList<String>(choices.size());
            for (int i = 0; i < choices.size(); i++) {
                Expr x = choices.get(i), y = x;
                while (true) {
                    if (y instanceof ExprUnary && ((ExprUnary) y).op == ExprUnary.Op.NOOP)
                        y = ((ExprUnary) y).sub;
                    else if (y instanceof ExprChoice && ((ExprChoice) y).choices.size() == 1)
                        y = ((ExprChoice) y).choices.get(0);
                    else
                        break;
                }
                if (y instanceof ExprBadCall) {
                    ExprBadCall bc = (ExprBadCall) y;
                    if (bc.args.size() < bc.fun.count()) {
                        ConstList<Expr> newargs = Util.append(bc.args, arg);
                        if (applicable(bc.fun, newargs))
                            y = ExprCall.make(bc.pos, bc.closingBracket, bc.fun, newargs, bc.extraWeight);
                        else
                            y = ExprBadCall.make(bc.pos, bc.closingBracket, bc.fun, newargs, bc.extraWeight);
                    } else {
                        y = ExprBinary.Op.JOIN.make(pos, closingBracket, arg, y);
                    }
                } else {
                    y = ExprBinary.Op.JOIN.make(pos, closingBracket, arg, x);
                }
                list.add(y);
                reasons.add(oldReasons.get(i));
            }
            return ExprChoice.make(isIntsNotUsed, rightPos, list.makeConst(), reasons.makeConst());
        }

        /** {@inheritDoc} */
        @Override
        public Expr visit(ExprList x) throws Err {
            TempList<Expr> temp = new TempList<Expr>(x.args.size());
            for (int i = 0; i < x.args.size(); i++)
                temp.add(visitThis(x.args.get(i)));
            return ExprList.make(x.pos, x.closingBracket, x.op, temp.makeConst());
        }

        /** {@inheritDoc} */
        @Override
        public Expr visit(ExprITE x) throws Err {
            Expr f = visitThis(x.cond);
            Expr a = visitThis(x.left);
            Expr b = visitThis(x.right);
            return ExprITE.make(x.pos, f, a, b);
        }

        /** {@inheritDoc} */
        @Override
        public Expr visit(ExprBadJoin x) throws Err {
            Expr left = visitThis(x.left);
            Expr right = visitThis(x.right);
            // If it's a macro invocation, instantiate it
            if (right instanceof Macro)
                return ((Macro) right).addArg(left).instantiate(this, warns);
            // check to see if it is the special builtin function "Int[]"
            if (left.type().is_int() && right.isSame(Sig.SIGINT))
                return left; // [AM] .cast2sigint();
            // otherwise, process as regular join or as method call
            left = left.typecheck_as_set();
            if (!left.errors.isEmpty() || !(right instanceof ExprChoice))
                return ExprBinary.Op.JOIN.make(x.pos, x.closingBracket, left, right);
            return process(x.pos, x.closingBracket, right.pos, ((ExprChoice) right).choices, ((ExprChoice) right).reasons, left);
        }

        /** {@inheritDoc} */
        @Override
        public Expr visit(ExprBinary x) throws Err {
            Expr left = visitThis(x.left);
            Expr right = visitThis(x.right);
            if (x.op == ExprBinary.Op.JOIN) {
                // If it's a macro invocation, instantiate it
                if (right instanceof Macro)
                    return ((Macro) right).addArg(left).instantiate(this, warns);
                // check to see if it is the special builtin function "Int[]"
                if (left.type().is_int() && right.isSame(Sig.SIGINT))
                    return left; // [AM] .cast2sigint();
                // otherwise, process as regular join or as method call
                left = left.typecheck_as_set();
                if (!left.errors.isEmpty() || !(right instanceof ExprChoice))
                    return x.op.make(x.pos, x.closingBracket, left, right);
                return process(x.pos, x.closingBracket, right.pos, ((ExprChoice) right).choices, ((ExprChoice) right).reasons, left);
            }
            return x.op.make(x.pos, x.closingBracket, left, right);
        }

        /** {@inheritDoc} */
        @Override
        public Expr visit(ExprLet x) throws Err {
            Expr right = visitThis(x.expr);
            right = right.resolve(right.type(), warns);
            ExprVar left = ExprVar.make(x.var.pos, x.var.label, right.type());
            put(left.label, left);
            Expr sub = visitThis(x.sub);
            remove(left.label);
            return ExprLet.make(x.pos, left, right, sub);
        }

        private boolean isOneOf(Expr x) {
            if (x.mult != 1 || x.type().arity() != 1)
                return false;
            while (x instanceof ExprUnary && ((ExprUnary) x).op == ExprUnary.Op.NOOP)
                x = ((ExprUnary) x).sub;
            return (x instanceof ExprUnary && ((ExprUnary) x).op == ExprUnary.Op.ONEOF);
        }

        /** {@inheritDoc} */
        @Override
        public Expr visit(ExprQt x) throws Err {
            TempList<Decl> decls = new TempList<Decl>(x.decls.size());
            boolean isMetaSig = false, isMetaField = false;
            for (Decl d : x.decls) {
                Expr exp = visitThis(d.expr).resolve_as_set(warns);
                if (exp.mult == 0 && exp.type().arity() == 1)
                    exp = ExprUnary.Op.ONEOF.make(null, exp);
                if (exp.errors.isEmpty()) {
                    if (exp.type().isSubtypeOf(rootmodule.metaSig().plus(rootmodule.metaField()).type())) {
                        isMetaSig = exp.type().intersects(rootmodule.metaSig().type());
                        isMetaField = exp.type().intersects(rootmodule.metaField().type());
                    }
                }
                // Below is a special case to allow more fine-grained
                // typechecking when we see "all x:field$" or "some x:field$"
                boolean some = (x.op == ExprQt.Op.SOME), compre = (x.op == ExprQt.Op.COMPREHENSION);
                if (x.decls.size() == 1 && d.names.size() == 1 && isOneOf(exp) && (x.op == ExprQt.Op.ALL || some || compre) && (isMetaSig || isMetaField)) {
                    ExprVar v = (ExprVar) (d.names.get(0));
                    // Prevent warnings
                    List<ErrorWarning> saved = warns;
                    warns = null;
                    // Now duplicate the body for each possible Meta Atom
                    // binding
                    Expr answer = null;
                    if (isMetaSig)
                        for (PrimSig child : rootmodule.metaSig().children())
                            if (child.type().intersects(exp.type())) {
                                put(v.label, child);
                                Expr sub = visitThis(x.sub);
                                remove(v.label);
                                if (compre)
                                    answer = child.in(exp).and(sub).ite(child, Sig.NONE).plus(answer);
                                else if (some)
                                    answer = child.in(exp).and(sub).or(answer);
                                else
                                    answer = child.in(exp).implies(sub).and(answer);
                            }
                    if (isMetaField)
                        for (PrimSig child : rootmodule.metaField().children())
                            if (child.type().intersects(exp.type())) {
                                put(v.label, child);
                                Expr sub = visitThis(x.sub);
                                remove(v.label);
                                if (compre)
                                    answer = child.in(exp).and(sub).ite(child, Sig.NONE).plus(answer);
                                else if (some)
                                    answer = child.in(exp).and(sub).or(answer);
                                else
                                    answer = child.in(exp).implies(sub).and(answer);
                            }
                    if (answer == null)
                        answer = (compre ? Sig.NONE : (some ? ExprConstant.FALSE : ExprConstant.TRUE));
                    else
                        answer = answer.resolve(answer.type(), null);
                    // Now, wrap the body in an ExprLet expression to prevent
                    // any more warnings by outer code
                    ExprVar combinedAnswer = ExprVar.make(Pos.UNKNOWN, "", answer.type());
                    Expr returnValue = ExprLet.make(Pos.UNKNOWN, combinedAnswer, answer, combinedAnswer);
                    // Restore the "warns" array, then return the answer
                    warns = saved;
                    return returnValue;
                }
                // Above is a special case to allow more fine-grained
                // typechecking when we see "all x:field$" or "some x:field$"
                TempList<ExprVar> n = new TempList<ExprVar>(d.names.size());
                for (ExprHasName v : d.names)
                    n.add(ExprVar.make(v.pos, v.label, exp.type()));
                Decl dd = new Decl(d.isPrivate, d.disjoint, d.disjoint2, null, n.makeConst(), exp);
                for (ExprHasName newname : dd.names)
                    put(newname.label, newname);
                decls.add(dd);
            }
            Expr sub = visitThis(x.sub);
            if (x.op == ExprQt.Op.SUM)
                sub = sub.resolve_as_int(warns);
            else
                sub = sub.resolve_as_formula(warns);
            for (Decl d : decls.makeConst())
                for (ExprHasName v : d.names)
                    remove(v.label);
            return x.op.make(x.pos, x.closingBracket, decls.makeConst(), sub);
        }

        /** {@inheritDoc} */
        @Override
        public Expr visit(ExprVar x) throws Err {
            Expr obj = resolve(x.pos, x.label);
            if (obj instanceof Macro) {
                Macro macro = ((Macro) obj).copy();
                Expr instantiated = macro.instantiate(this, warns);
                instantiated.setReferenced(new Clause() {

                    @Override
                    public Pos pos() {
                        return instantiated.pos;
                    }

                    @Override
                    public String explain() {
                        return instantiated.toString();
                    }

                });
                return instantiated;
            } else
                return obj;
        }

        /** {@inheritDoc} */
        @Override
        public Expr visit(ExprUnary x) throws Err {
            return x.op.make(x.pos, visitThis(x.sub));
        }

        /** {@inheritDoc} */
        @Override
        public Expr visit(ExprCall x) {
            return x;
        }

        /** {@inheritDoc} */
        @Override
        public Expr visit(ExprConstant x) {
            return x;
        }

        /** {@inheritDoc} */
        @Override
        public Expr visit(Sig x) {
            return x;
        }

        /** {@inheritDoc} */
        @Override
        public Expr visit(Field x) {
            return x;
        }

    }

    // ============================================================================================================================//

    /**
     * Mutable; this class represents an untypechecked Alloy module import
     * statement; equals() uses object identity.
     */
    public static final class Open implements Clause {

        /**
         * The position in the original model where this "open" statement was declared;
         * never null.
         */
        public final Pos               pos;

        /**
         * The alias for this open declaration; always a nonempty string.
         */
        public final String            alias;

        /** The unmodifiable list of instantiating arguments. */
        public final ConstList<String> args;

        /**
         * The relative filename for the file being imported, without the final ".als"
         * part; always a nonempty string.
         */
        public final String            filename;

        /** Whether this is a private open or not. */
        final boolean                  isPrivate;

        /**
         * The actual Module object that it points to; null until we resolve it.
         */
        private CompModule             realModule = null;

        private List<Expr>             expressions;

        /**
         * Returns the actual Module object that it points to; null if we have not
         * resolved it.
         */
        public CompModule getRealModule() {
            return realModule;
        }

        /**
         * Constructs an Open object.
         *
         * @param expressions
         */
        private Open(Pos pos, boolean isPrivate, String alias, ConstList<String> args, String filename, List<Expr> expressions) {
            this.pos = pos;
            this.isPrivate = isPrivate;
            this.alias = alias;
            this.args = args;
            this.filename = filename;
            this.expressions = expressions;
        }

        /**
         * Connect this OPEN statement to a module that it points to.
         */
        void connect(CompModule realModule) throws Err {
            if (this.realModule != null && this.realModule != realModule)
                throw new ErrorFatal("Internal error (import mismatch)");
            this.realModule = realModule;
        }

        public void setResolvedFilePath(String cp) {
            if (expressions != null && !expressions.isEmpty()) {
                expressions.get(0).setReferenced(new ModuleReference(cp));
            }

        }

        @Override
        public Pos pos() {
            return pos;
        }

        @Override
        public String explain() {
            StringBuilder sb = new StringBuilder();
            sb.append("open ");
            sb.append(filename);
            for (String arg : args) {
                sb.append("[").append(arg).append("]");
            }
            if (alias != null) {
                sb.append(" as ").append(alias);
            }
            return sb.toString();
        }
    }

    // ============================================================================================================================//

    /**
     * Constructs a new CompModule object
     *
     * @param world - the world that this CompModule belongs to (null if this is the
     *            beginning of a new World)
     * @param filename - the filename corresponding to this module
     * @param path - one of the path pointing to this module
     */
    CompModule(CompModule world, String filename, String path) throws Err {
        if (world == null) {
            if (path.length() > 0)
                throw new ErrorFatal("Root module misparsed by parser.");
            this.world = this;
            new2old = new LinkedHashMap<Sig,Sig>();
            old2fields = new LinkedHashMap<Sig,List<Decl>>();
            old2appendedfacts = new LinkedHashMap<Sig,Expr>();
            sig2module = new HashMap<Sig,CompModule>();
            allModules = new ArrayList<CompModule>();
            exactSigs = new LinkedHashSet<Sig>();
            globals = new LinkedHashMap<String,Expr>();
            metaSig = new PrimSig("this/sig$", Attr.ABSTRACT, Attr.META);
            metaField = new PrimSig("this/field$", Attr.ABSTRACT, Attr.META);
        } else {
            this.world = world;
            new2old = world.new2old;
            old2fields = world.old2fields;
            old2appendedfacts = world.old2appendedfacts;
            sig2module = world.sig2module;
            allModules = world.allModules;
            exactSigs = world.exactSigs;
            globals = world.globals;
            metaSig = world.metaSig;
            metaField = world.metaField;
        }
        this.path = path;
        if (filename != null && filename.length() > 0)
            this.modulePos = new Pos(filename, 1, 1);
    }

    /** {@inheritDoc} */
    @Override
    public final Pos pos() {
        return modulePos;
    }

    /** {@inheritDoc} */
    @Override
    public final Pos span() {
        return modulePos;
    }

    /** {@inheritDoc} */
    @Override
    public String getHTML() {
        StringBuilder sb = new StringBuilder("<b>module</b> ").append(path).append(" <i>");
        Util.encodeXML(sb, modulePos.filename);
        return sb.append("</i>").toString();
    }

    /** {@inheritDoc} */
    @Override
    public List< ? extends Browsable> getSubnodes() {
        ArrayList<Browsable> ans = new ArrayList<Browsable>();
        ArrayList<Browsable> x;
        if (opens.size() > 0) {
            x = new ArrayList<Browsable>(opens.size());
            for (Open e : opens.values())
                if (!x.contains(e.realModule))
                    x.add(e.realModule);
            ans.add(make("<b>" + x.size() + (x.size() > 1 ? " opens</b>" : " open</b>"), x));
        }
        if (sigs.size() > 0) {
            x = new ArrayList<Browsable>(sigs.values());
            ans.add(make("<b>" + x.size() + (x.size() > 1 ? " sigs</b>" : " sig</b>"), x));
        }
        if (funcs.size() > 0) {
            ArrayList<Browsable> x2 = new ArrayList<Browsable>(funcs.size());
            x = new ArrayList<Browsable>(funcs.size());
            for (ArrayList<Func> e : funcs.values())
                for (Func f : e)
                    if (f.isPred)
                        x.add(f);
                    else
                        x2.add(f);
            if (x.size() > 0)
                ans.add(make("<b>" + x.size() + (x.size() > 1 ? " preds</b>" : " pred</b>"), x));
            if (x2.size() > 0)
                ans.add(make("<b>" + x2.size() + (x2.size() > 1 ? " funs</b>" : " fun</b>"), x2));
        }
        if (commands.size() > 0) {
            ArrayList<Browsable> x2 = new ArrayList<Browsable>(commands.size());
            x = new ArrayList<Browsable>(commands.size());
            for (Command e : commands)
                if (e.check)
                    x.add(e);
                else
                    x2.add(e);
            if (x.size() > 0)
                ans.add(make("<b>" + x.size() + (x.size() > 1 ? " checks</b>" : " check</b>"), x));
            if (x2.size() > 0)
                ans.add(make("<b>" + x2.size() + (x2.size() > 1 ? " runs</b>" : " run</b>"), x2));
        }
        if (facts.size() > 0) {
            x = new ArrayList<Browsable>(facts.size());
            for (Pair<String,Expr> e : facts)
                x.add(make(e.b.span(), e.b.span(), "<b>fact " + e.a + "</b>", e.b));
            ans.add(make("<b>" + x.size() + (x.size() > 1 ? " facts</b>" : " fact</b>"), x));
        }
        if (asserts.size() > 0) {
            x = new ArrayList<Browsable>(asserts.size());
            for (Map.Entry<String,Expr> e : asserts.entrySet()) {
                Pos sp = e.getValue().span();
                x.add(make(sp, sp, "<b>assert</b> " + e.getKey(), e.getValue()));
            }
            ans.add(make("<b>" + x.size() + (x.size() > 1 ? " asserts</b>" : " assert</b>"), x));
        }
        return ans;
    }

    /**
     * Returns the meta signature "sig$" (or null if such a sig does not exist)
     */
    public PrimSig metaSig() {
        return world.metaSig;
    }

    /**
     * Returns the meta signature "field$" (or null if such a sig does not exist)
     */
    public PrimSig metaField() {
        return world.metaField;
    }

    private static String base(String string) {
        int i = string.lastIndexOf('/');
        return i < 0 ? string : string.substring(i + 1);
    }

    private static String base(Sig sig) {
        return base(sig.label);
    }

    /**
     * Generate an error message saying the given keyword is no longer supported.
     */
    static ErrorSyntax hint(Pos pos, String name) {
        String msg = "The name \"" + name + "\" cannot be found.";
        if ("exh".equals(name) || "exhaustive".equals(name) || "part".equals(name) || "partition".equals(name))
            msg = msg + " If you are migrating from Alloy 3, please see Help->QuickGuide on how to translate models that use the \"" + name + "\" keyword.";
        return new ErrorSyntax(pos, msg);
    }

    /**
     * Parse one expression by starting fromt this module as the root module.
     */
    @Override
    public Expr parseOneExpressionFromString(String input) throws Err, FileNotFoundException, IOException {
        Map<String,String> fc = new LinkedHashMap<String,String>();
        fc.put("", "run {\n" + input + "}"); // We prepend the line "run{"
        CompModule m = CompUtil.parse(new ArrayList<Object>(), null, fc, null, -1, "", "", 1);
        if (m.funcs.size() == 0)
            throw new ErrorSyntax("The input does not correspond to an Alloy expression.");
        Expr body = m.funcs.values().iterator().next().get(0).getBody();
        Context cx = new Context(this, null);
        body = cx.check(body);
        body = body.resolve(body.type(), null);
        if (body.errors.size() > 0)
            throw body.errors.pick();
        else
            return body;
    }

    /**
     * Throw an exception if the name is already used, or has @ or /, or is
     * univ/Int/none.
     */
    private void dup(Pos pos, String name, boolean checkSig) throws Err {
        if (name.length() == 0)
            throw new ErrorSyntax(pos, "Name cannot be empty");
        if (name.indexOf('@') >= 0)
            throw new ErrorSyntax(pos, "Name cannot contain the \'@\' character");
        if (name.indexOf('/') >= 0)
            throw new ErrorSyntax(pos, "Name cannot contain the \'/\' character");
        if (name.equals("univ"))
            throw new ErrorSyntax(pos, "\'univ\' is a reserved keyword.");
        if (name.equals("Int"))
            throw new ErrorSyntax(pos, "\'Int\' is a reserved keyword.");
        if (name.equals("none"))
            throw new ErrorSyntax(pos, "\'none\' is a reserved keyword.");
        if (checkSig && (params.containsKey(name) || sigs.containsKey(name)))
            throw new ErrorSyntax(pos, "\"" + name + "\" is already the name of a sig/parameter in this module.");
    }

    /**
     * Throw an exception if there are more than 1 match; return nonnull if only one
     * match; return null if no match.
     */
    private Object unique(Pos pos, String name, List<Object> objs) throws Err {
        if (objs.size() == 0)
            return null;
        if (objs.size() == 1)
            return objs.get(0);
        StringBuilder msg = new StringBuilder("The name \"").append(name);
        msg.append("\" is ambiguous.\n" + "There are ").append(objs.size()).append(" choices:");
        for (int i = 0; i < objs.size(); i++) {
            msg.append("\n\n#").append(i + 1).append(": ");
            Object x = objs.get(i);
            if (x instanceof Sig) {
                Sig y = (Sig) x;
                msg.append("sig ").append(y.label).append("\n" + "at ").append(y.pos.toShortString());
            } else if (x instanceof Func) {
                Func y = (Func) x;
                msg.append(y.isPred ? "pred " : "fun ").append(y.label).append("\n" + "at ").append(y.pos.toShortString());
            } else if (x instanceof Expr) {
                Expr y = (Expr) x;
                msg.append("assertion at ").append(y.pos.toShortString());
            }
        }
        throw new ErrorSyntax(pos, msg.toString());
    }

    /**
     * Returns a list containing THIS MODULE and all modules reachable from this
     * module.
     */
    private void getHelper(int level, SafeList<CompModule> ans, Object key) {
        if (visitedBy == key)
            return;
        visitedBy = key;
        ans.add(this);
        for (Open i : opens.values())
            if (!(level > 0 && i.isPrivate)) {
                CompModule m = i.realModule;
                if (m != null)
                    m.getHelper(level < 0 ? (-1) : (level + 1), ans, key);
            }
    }

    /**
     * Return the list containing THIS MODULE and all modules reachable from this
     * module.
     */
    @Override
    public SafeList<CompModule> getAllReachableModules() {
        SafeList<CompModule> ans = new SafeList<CompModule>();
        getHelper(-1, ans, new Object()); // The object must be new, since we
                                         // need it to be a unique key
        return ans.dup();
    }

    /**
     * Return the list of all relative filenames included from this MODULE.
     */
    @Override
    public List<String> getAllReachableModulesFilenames() {
        Set<String> set = new LinkedHashSet<String>();
        for (Open o : opens.values())
            set.add(o.filename);
        return new ArrayList<String>(set);
    }

    /**
     * Return the list containing THIS MODULE and all modules nameable from this
     * module.
     */
    private SafeList<CompModule> getAllNameableModules() {
        SafeList<CompModule> ans = new SafeList<CompModule>();
        getHelper(0, ans, new Object()); // The object must be new, since we
                                        // need it to be a unique key
        return ans.dup();
    }

    /**
     * Return the list containing UNIV, SIGINT, SEQIDX, STRING, NONE, and all sigs
     * defined in this module or a reachable submodule.
     */
    @Override
    public ConstList<Sig> getAllReachableSigs() {
        TempList<Sig> x = new TempList<Sig>();
        x.add(UNIV);
        x.add(SIGINT);
        x.add(SEQIDX);
        x.add(STRING);
        x.add(NONE);
        x.addAll(getAllReachableUserDefinedSigs());
        return x.makeConst();
    }

    /**
     * Return the list containing all sigs defined in this module or a reachable
     * submodule.
     */
    @Override
    public ConstList<Sig> getAllReachableUserDefinedSigs() {
        TempList<Sig> x = new TempList<Sig>();
        for (CompModule m : getAllReachableModules())
            x.addAll(m.sigs.values());
        return x.makeConst();
    }

    /**
     * Lookup non-fully-qualified Sig/Func/Assertion from the current module; it
     * skips PARAMs.
     */
    private List<Object> getRawNQS(CompModule start, final int r, String name) {
        // (r&1)!=0 => Sig, (r&2) != 0 => assertion, (r&4)!=0 => Func
        List<Object> ans = new ArrayList<Object>();
        for (CompModule m : getAllNameableModules()) {
            if ((r & 1) != 0) {
                Sig x = m.sigs.get(name);
                if (x != null)
                    if (m == start || x.isPrivate == null)
                        ans.add(x);
            }
            if ((r & 2) != 0) {
                Expr x = m.asserts.get(name);
                if (x != null)
                    ans.add(x);
            }
            if ((r & 4) != 0) {
                ArrayList<Func> x = m.funcs.get(name);
                if (x != null)
                    for (Func y : x)
                        if (m == start || y.isPrivate == null)
                            ans.add(y);
            }
        }
        return ans;
    }

    /**
     * Lookup a fully-qualified Sig/Func/Assertion from the current module; it skips
     * PARAMs.
     */
    private List<Object> getRawQS(final int r, String name) {
        // (r&1)!=0 => Sig, (r&2) != 0 => assertion, (r&4)!=0 => Func
        List<Object> ans = new ArrayList<Object>();
        CompModule u = this;
        if (name.startsWith("this/"))
            name = name.substring(5);
        for (int level = 0;; level++) {
            int i = name.indexOf('/');
            if (i < 0) {
                if ((r & 1) != 0) {
                    Sig x = u.sigs.get(name);
                    if (x != null)
                        if (level == 0 || x.isPrivate == null)
                            ans.add(x);
                }
                if ((r & 2) != 0) {
                    Expr x = u.asserts.get(name);
                    if (x != null)
                        ans.add(x);
                }
                if ((r & 4) != 0) {
                    ArrayList<Func> x = u.funcs.get(name);
                    if (x != null)
                        for (Func y : x)
                            if (level == 0 || y.isPrivate == null)
                                ans.add(y);
                }
                if (ans.size() == 0)
                    return u.getRawNQS(this, r, name); // If nothing at this
                                                      // module, then do a
                                                      // non-qualified search
                                                      // from this module
                return ans;
            }
            String alias = name.substring(0, i);
            Open uu = u.opens.get(alias);
            if (uu == null || uu.realModule == null)
                return ans; // may happen during the initial "module"
            if (level > 0 && uu.isPrivate)
                return ans; // that means the module is imported privately
            u = uu.realModule;
            name = name.substring(i + 1);
        }
    }

    /**
     * Lookup a Sig from the current module (and it will also search this.params)
     */
    private Sig getRawSIG(Pos pos, String name) throws Err {
        List<Object> s;
        Sig s2 = null;
        if (name.equals("sig$") || name.equals("field$"))
            if (world != null) {
                s2 = world.sigs.get(name);
                if (s2 != null)
                    return s2;
            }
        if (name.equals("univ"))
            return UNIV;
        if (name.equals("Int"))
            return SIGINT;
        if (name.equals("seq/Int"))
            return SEQIDX;
        if (name.equals("String"))
            return STRING;
        if (name.equals("none"))
            return NONE;
        if (name.indexOf('/') < 0) {
            s = getRawNQS(this, 1, name);
            s2 = params.get(name);
        } else {
            if (name.startsWith("this/")) {
                name = name.substring(5);
                s2 = params.get(name);
            }
            s = getRawQS(1, name);
        }
        if (s2 != null && !s.contains(s2))
            s.add(s2);
        return (Sig) (unique(pos, name, s));
    }

    /** Returns a short description for this module. */
    @Override
    public String toString() {
        return "module{" + path + "}";
    }

    // ============================================================================================================================//

    /** Returns a pointer to the root module in this world. */
    public CompModule getRootModule() {
        return world;
    }

    /**
     * Returns the text of the "MODULE" line at the top of the file; "unknown" if
     * the line has not be parsed from the file yet.
     */
    @Override
    public String getModelName() {
        return moduleName;
    }

    /**
     * Returns an unmodifiable copy of the current list of OPEN statements.
     */
    public ConstList<Open> getOpens() {
        return ConstList.make(opens.values());
    }

    /** Add the "MODULE" declaration. */
    void addModelName(Pos pos, String moduleName, List<ExprVar> list) throws Err {
        if (status > 0)
            throw new ErrorSyntax(pos, "The \"module\" declaration must occur at the top,\n" + "and can occur at most once.");
        this.moduleName = moduleName;
        this.modulePos = pos;
        boolean nextIsExact = false;
        if (list != null)
            for (ExprVar expr : list) {
                if (expr == null) {
                    nextIsExact = true;
                    continue;
                }
                String name = expr.label;
                dup(expr.span(), name, true);
                if (path.length() == 0) {
                    Sig newSig = addSig(name, null, null, null, null, WHERE.make(expr.span()));
                    if (nextIsExact)
                        exactSigs.add(newSig);
                } else {
                    params.put(name, null);
                    if (nextIsExact)
                        exactParams.add(name);
                }
                nextIsExact = false;
            }
        this.status = 1; // This line must be at the end, since "addSig" will
                        // otherwise bump the status value to 3
    }

    /** Add util/sequniv to the list of declarations. */
    void addSeq(Pos pos) throws Err {
        int oldStatus = status;
        status = 0;
        try {
            addOpen(pos, null, ExprVar.make(pos, "util/sequniv"), null, ExprVar.make(pos, "seq"));
        } finally {
            status = oldStatus;
        }
    }

    /** Add an OPEN declaration. */
    void addOpen(Pos pos, Pos isPrivate, ExprVar name, List<ExprVar> args, ExprVar alias) throws Err {
        if (status > 2)
            throw new ErrorSyntax(pos, "The \"open\" declaration must occur before any\n" + "sig/pred/fun/fact/assert/check/run command.");
        String as = (alias == null ? "" : alias.label);
        if (name.label.length() == 0)
            throw new ErrorSyntax(name.span(), "The filename cannot be empty.");
        if (as.indexOf('$') >= 0)
            throw new ErrorSyntax(alias == null ? null : alias.span(), "Alias must not contain the \'$\' character");
        if (as.indexOf('@') >= 0)
            throw new ErrorSyntax(alias == null ? null : alias.span(), "Alias must not contain the \'@\' character");
        if (as.indexOf('/') >= 0)
            throw new ErrorSyntax(alias == null ? null : alias.span(), "Alias must not contain the \'/\' character");
        if (as.length() == 0) {
            as = "open$" + (1 + opens.size());
            if (args == null || args.size() == 0) {
                for (int i = 0;; i++) {
                    if (i >= name.label.length()) {
                        as = name.label;
                        break;
                    }
                    char c = name.label.charAt(i);
                    if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z'))
                        continue;
                    if (i == 0)
                        break;
                    if (!(c >= '0' && c <= '9') && c != '_' && c != '\'' && c != '\"')
                        break;
                }
            }
        }
        final TempList<String> newlist = new TempList<String>(args == null ? 0 : args.size());
        if (args != null)
            for (int i = 0; i < args.size(); i++) {
                ExprVar arg = args.get(i);
                if (arg.label.length() == 0)
                    throw new ErrorSyntax(arg.span(), "Argument cannot be empty.");
                if (arg.label.indexOf('@') >= 0)
                    throw new ErrorSyntax(arg.span(), "Argument cannot contain the \'@\' chracter.");
                newlist.add(arg.label);
            }
        Open x = opens.get(as);
        if (x != null) {
            // we allow this, especially because of util/sequniv
            if (x.args.equals(newlist.makeConst()) && x.filename.equals(name.label))
                return;
            throw new ErrorSyntax(pos, "You cannot import two different modules\n" + "using the same alias.");
        }
        List<Expr> expressions = new ArrayList<>(args == null ? Collections.emptySet() : args);
        expressions.add(0, name);
        expressions.add(alias);
        x = new Open(pos, isPrivate != null, as, newlist.makeConst(), name.label, expressions);
        opens.put(as, x);
    }

    /** Do any post-parsing processig. */
    void doneParsing() {
        status = 3;
        LinkedHashMap<String,Open> copy = new LinkedHashMap<String,Open>(opens);
        opens.clear();
        for (Map.Entry<String,Open> e : copy.entrySet()) {
            String a = e.getKey();
            Open m = e.getValue();
            if (a.indexOf('$') >= 0) {
                String base = m.filename;
                int i = base.lastIndexOf('/');
                if (i >= 0)
                    base = base.substring(i + 1);
                if (!copy.containsKey(base) && !opens.containsKey(base)) {
                    for (i = 0; i < base.length(); i++) {
                        char c = base.charAt(i);
                        if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z'))
                            continue;
                        if (i != 0 && ((c >= '0' && c <= '9') || c == '_' || c == '\'' || c == '\"'))
                            continue;
                        break;
                    }
                    if (i >= base.length())
                        a = base;
                }
            }
            opens.put(a, new Open(m.pos, m.isPrivate, a, m.args, m.filename, m.expressions));
        }
    }

    /**
     * Every param in every module will now point to a nonnull Sig.
     */
    private static void resolveParams(A4Reporter rep, List<CompModule> modules) throws Err {
        while (true) {
            boolean chg = false;
            Open missing = null;
            String missingName = "";
            for (CompModule mod : modules)
                for (Open open : mod.opens.values()) {
                    CompModule sub = open.realModule;
                    if (open.args.size() != sub.params.size())
                        throw new ErrorSyntax(open.pos, "You supplied " + open.args.size() + " arguments to the open statement, but the imported module requires " + sub.params.size() + " arguments.");
                    int i = 0;
                    for (Map.Entry<String,Sig> p : sub.params.entrySet()) {
                        Sig old = p.getValue();
                        String kn = p.getKey(), vn = open.args.get(i);
                        i++;
                        Sig vv = mod.getRawSIG(open.pos, vn);
                        if (vv == null) {
                            if (old == null) {
                                missing = open;
                                missingName = vn;
                            }
                            continue;
                        }
                        if (old == vv)
                            continue;
                        if (old != null)
                            throw new ErrorFatal(open.pos, "Internal error (module re-instantiated with different arguments)");
                        if (vv == NONE)
                            throw new ErrorSyntax(open.pos, "You cannot use \"none\" as an instantiating argument.");
                        chg = true;
                        p.setValue(vv);
                        rep.parse("RESOLVE: " + (sub.path.length() == 0 ? "this/" : sub.path) + "/" + kn + " := " + vv + "\n");
                    }
                }
            if (!chg && missing == null)
                return;
            if (!chg)
                throw new ErrorSyntax(missing.pos, "The signature name \"" + missingName + "\" cannot be found.");
        }
    }

    /**
     * Modules with same filename and instantiating arguments will be merged.
     */
    private static void resolveModules(A4Reporter rep, List<CompModule> modules) {
        // Before merging, the only pointers that go between Module objects are
        // (1) a module's "params" may point to a sig in another module
        // (2) a module's "imports" may point to another module
        // So when we find that two modules A and B should be merged,
        // we go through every module and replace "pointers into B" with
        // equivalent "pointers into A".
        while (true) {
            boolean chg = false;
            for (int i = 0; i < modules.size(); i++) {
                CompModule a = modules.get(i);
                for (int j = i + 1; j < modules.size(); j++) {
                    CompModule b = modules.get(j);
                    if (!a.modulePos.filename.equals(b.modulePos.filename) || !a.params.equals(b.params))
                        continue;
                    chg = true;
                    rep.parse("MATCH FOUND ON " + a.modulePos.filename + "\n");
                    int aa = a.path.indexOf('$'), bb = b.path.indexOf('$');
                    if (i != 0)
                        if (!(aa < 0 && bb >= 0))
                            if ((aa >= 0 && bb < 0) || Util.slashComparator.compare(a.path, b.path) > 0) {
                                a = b;
                                b = modules.get(i);
                                modules.set(i, a);
                            }
                    modules.remove(j);
                    j--;
                    for (CompModule c : modules) {
                        for (Map.Entry<String,Sig> p : c.params.entrySet())
                            if (isin(p.getValue(), b.sigs))
                                p.setValue(a.sigs.get(base(p.getValue())));
                        for (Open p : c.opens.values())
                            if (p.realModule == b)
                                p.realModule = a;
                    }
                }
            }
            if (!chg)
                break;
        }
    }

    // ============================================================================================================================//

    /** Add a sig declaration. */
    void addGhostSig() throws Err {
        sigs.put(Sig.GHOST.label, Sig.GHOST);
    }

    Sig addSig(String name, ExprVar par, List<ExprVar> parents, List<Decl> fields, Expr fact, Attr... attributes) throws Err {
        Sig obj;
        Pos pos = Pos.UNKNOWN.merge(WHERE.find(attributes));
        status = 3;
        dup(pos, name, true);
        String full = (path.length() == 0) ? "this/" + name : path + "/" + name;
        Pos subset = null, subsig = null;
        boolean exact = false;
        if (par != null) {
            if (par.label.equals("extends")) {
                subsig = par.span().merge(parents.get(0).span());
            } else {
                exact = !par.label.equals("in");
                subset = par.span();
                for (ExprVar p : parents)
                    subset = p.span().merge(subset);
            }
        }
        attributes = Util.append(attributes, exact ? Attr.EXACT : null);
        if (subset != null) {
            attributes = Util.append(attributes, SUBSET.makenull(subset));
            List<Sig> newParents = new ArrayList<Sig>(parents == null ? 0 : parents.size());
            if (parents != null)
                for (ExprVar p : parents)
                    newParents.add(new PrimSig(p.label, WHERE.make(p.pos)));
            obj = new SubsetSig(full, newParents, attributes);
        } else {
            attributes = Util.append(attributes, SUBSIG.makenull(subsig));
            PrimSig newParent = (parents != null && parents.size() > 0) ? (new PrimSig(parents.get(0).label, WHERE.make(parents.get(0).pos))) : UNIV;
            obj = new PrimSig(full, newParent, attributes);
        }
        sigs.put(name, obj);
        old2fields.put(obj, fields);
        old2appendedfacts.put(obj, fact);
        return obj;
    }

    /** Add an enumeration. */
    void addEnum(Pos pos, Pos priv, ExprVar name, List<ExprVar> atoms, Pos closingBracket) throws Err {
        ExprVar EXTENDS = ExprVar.make(null, "extends");
        ExprVar THIS = ExprVar.make(null, "this/" + name);
        List<ExprVar> THESE = Arrays.asList(THIS);
        if (atoms == null || atoms.size() == 0)
            throw new ErrorSyntax(pos, "Enumeration must contain at least one name.");
        addSig(name.label, null, null, null, null, WHERE.make(name.pos), ABSTRACT.make(name.pos), PRIVATE.makenull(priv), Attr.ENUM);
        for (ExprVar a : atoms)
            addSig(a.label, EXTENDS, THESE, null, null, WHERE.make(a.pos), ONE.make(a.pos), PRIVATE.makenull(priv));
        int oldStatus = status;
        status = 0;
        try {
            addOpen(null, null, ExprVar.make(pos, "util/ordering"), Arrays.asList(THIS), null);
        } finally {
            status = oldStatus;
        }
    }

    /** The given Sig will now point to a nonnull Sig. */
    private static Sig resolveSig(CompModule res, Set<Object> topo, Sig oldS, final List<ErrorWarning> warns) throws Err {
        // When typechecking each sig:
        // * a static sig should NOT be included in a variable sig [electrum]
        // * a static sig should NOT extend a variable sig [electrum]
        // * a variable sig should NOT extend a static sig [electrum]
        if (res.new2old.containsKey(oldS))
            return oldS;
        Sig realSig;
        final Pos pos = oldS.pos;
        final CompModule u = res.sig2module.get(oldS);
        final String name = base(oldS);
        final String fullname = (u.path.length() == 0) ? ("this/" + name) : (u.path + "/" + name);
        if (!topo.add(oldS))
            throw new ErrorType(pos, "Sig " + oldS + " is involved in a cyclic inheritance.");
        if (oldS instanceof SubsetSig) {
            List<Sig> parents = new ArrayList<Sig>();
            for (Sig n : ((SubsetSig) oldS).parents) {
                Sig parentAST = u.getRawSIG(n.pos, n.label);
                if (parentAST == null)
                    throw new ErrorSyntax(n.pos, "The sig \"" + n.label + "\" cannot be found.");
                parents.add(resolveSig(res, topo, parentAST, warns));
            }
            realSig = new SubsetSig(fullname, parents, oldS.attributes.toArray(new Attr[0]));
            for (Sig n : parents)
                if (n != UNIV && n.isVariable != null && realSig.isVariable == null)
                    warns.add(new ErrorWarning(realSig.isSubset, "Part of " + n.label + " is static.\n" + "Sig " + realSig.label + " is static but " + n.label + " is variable."));
        } else {
            Sig sup = ((PrimSig) oldS).parent;
            Sig parentAST = u.getRawSIG(sup.pos, sup.label);
            if (parentAST == null)
                throw new ErrorSyntax(sup.pos, "The sig \"" + sup.label + "\" cannot be found.");
            Sig parent = resolveSig(res, topo, parentAST, warns);
            if (!(parent instanceof PrimSig))
                throw new ErrorSyntax(sup.pos, "Cannot extend the subset signature \"" + parent + "\".\n" + "A signature can only extend a toplevel signature or a subsignature.");
            PrimSig p = (PrimSig) parent;
            realSig = new PrimSig(fullname, p, oldS.attributes.toArray(new Attr[0]));
            if (parent != UNIV && parent.isVariable != null && realSig.isVariable == null)
                warns.add(new ErrorWarning(realSig.isSubsig, "Part of " + parent.label + " is static.\n" + "Sig " + realSig.label + " is static but " + parent.label + " is variable."));
            if (parent != UNIV && parent.isVariable == null && realSig.isVariable != null)
                warns.add(new ErrorWarning(realSig.isSubsig, "Marking sig " + realSig.label + " as var is redundant.\n" + "Sig " + realSig.label + " is variable but " + parent.label + " is static."));
        }
        res.new2old.put(realSig, oldS);
        res.sig2module.put(realSig, u);
        for (CompModule m : res.allModules) {
            for (Map.Entry<String,Sig> e : m.sigs.entrySet())
                if (e.getValue() == oldS)
                    e.setValue(realSig);
            for (Map.Entry<String,Sig> e : m.params.entrySet())
                if (e.getValue() == oldS)
                    e.setValue(realSig);
        }
        if (res.exactSigs.remove(oldS))
            res.exactSigs.add(realSig);
        return realSig;
    }

    /**
     * Returns an unmodifiable list of all signatures defined inside this module.
     */
    @Override
    public SafeList<Sig> getAllSigs() {
        return new SafeList<Sig>(sigs.values());
        // SafeList<Sig> x = new SafeList<Sig>(sigs.values());
        // return x.dup();
    }

    // ============================================================================================================================//

    /** Add a MACRO declaration. */
    void addMacro(Pos p, Pos isPrivate, String n, List<ExprVar> decls, Expr v) throws Err {
        if (!Version.experimental)
            throw new ErrorSyntax(p, "LET declaration is allowed only inside a toplevel paragraph.");
        ConstList<ExprVar> ds = ConstList.make(decls);
        status = 3;
        dup(p, n, false);
        for (int i = 0; i < ds.size(); i++)
            for (int j = i + 1; j < ds.size(); j++)
                if (ds.get(i).label.equals(ds.get(j).label))
                    throw new ErrorSyntax(ds.get(j).span(), "The parameter name \"" + ds.get(j).label + "\" cannot appear more than once.");
        Macro ans = new Macro(p, isPrivate, this, n, ds, v);
        Macro old = macros.put(n, ans);
        if (old != null) {
            macros.put(n, old);
            throw new ErrorSyntax(p, "You cannot declare more than one macro with the same name \"" + n + "\" in the same file.");
        }
    }

    /** Add a FUN or PRED declaration. */
    void addFunc(Pos p, Pos isPrivate, String n, Expr f, List<Decl> decls, Expr t, Expr v) throws Err {
        if (decls == null)
            decls = new ArrayList<Decl>();
        else
            decls = new ArrayList<Decl>(decls);
        if (f != null)
            decls.add(0, new Decl(null, null, null, null, Util.asList(ExprVar.make(f.span(), "this")), f));
        for (Decl d : decls) {
            if (d.isPrivate != null) {
                ExprHasName name = d.names.get(0);
                throw new ErrorSyntax(d.isPrivate.merge(name.pos), "Function parameter \"" + name.label + "\" is always private already.");
            }
            if (d.disjoint2 != null) {
                ExprHasName name = d.names.get(d.names.size() - 1);
                throw new ErrorSyntax(d.disjoint2.merge(name.pos), "Function parameter \"" + name.label + "\" cannot be bound to a 'disjoint' expression.");
            }
        }
        status = 3;
        dup(p, n, false);
        ExprHasName dup = Decl.findDuplicateName(decls);
        if (dup != null)
            throw new ErrorSyntax(dup.span(), "The parameter name \"" + dup.label + "\" cannot appear more than once.");
        Func ans = new Func(p, isPrivate, n, decls, t, v);
        ArrayList<Func> list = funcs.get(n);
        if (list == null) {
            list = new ArrayList<Func>();
            funcs.put(n, list);
        }
        list.add(ans);
    }

    /** Each FunAST will now point to a bodyless Func object. */
    private JoinableList<Err> resolveFuncDecls(A4Reporter rep, JoinableList<Err> errors, List<ErrorWarning> warns) throws Err {
        for (ArrayList<Func> list : funcs.values()) {
            for (int listi = 0; listi < list.size(); listi++) {
                Func f = list.get(listi);
                String fullname = (path.length() == 0 ? "this/" : (path + "/")) + f.label;
                // Each PARAMETER can refer to earlier parameter in the same
                // function, and any SIG or FIELD visible from here.
                // Each RETURNTYPE can refer to the parameters of the same
                // function, and any SIG or FIELD visible from here.
                Context cx = new Context(this, warns);
                cx.rootfunparam = true;
                TempList<Decl> tmpdecls = new TempList<Decl>();
                boolean err = false;
                for (Decl d : f.decls) {
                    TempList<ExprVar> tmpvars = new TempList<ExprVar>();
                    Expr val = cx.check(d.expr).resolve_as_set(warns);
                    if (!val.errors.isEmpty()) {
                        err = true;
                        errors = errors.make(val.errors);
                    }
                    for (ExprHasName n : d.names) {
                        ExprVar v = ExprVar.make(n.span(), n.label, val.type());
                        cx.put(n.label, v);
                        tmpvars.add(v);
                        rep.typecheck((f.isPred ? "pred " : "fun ") + fullname + ", Param " + n.label + ": " + v.type() + "\n");
                    }
                    tmpdecls.add(new Decl(d.isPrivate, d.disjoint, d.disjoint2, null, tmpvars.makeConst(), val));
                }
                Expr ret = null;
                if (!f.isPred) {
                    ret = cx.check(f.returnDecl).resolve_as_set(warns);
                    if (!ret.errors.isEmpty()) {
                        err = true;
                        errors = errors.make(ret.errors);
                    }
                }
                if (err)
                    continue;
                try {
                    f = new Func(f.pos, f.isPrivate, fullname, tmpdecls.makeConst(), ret, f.getBody());
                    list.set(listi, f);
                    rep.typecheck("" + f + ", RETURN: " + f.returnDecl.type() + "\n");
                } catch (Err ex) {
                    errors = errors.make(ex);
                }
            }
        }
        return errors;
    }

    /** Each Func's body will now be typechecked Expr object. */
    private JoinableList<Err> resolveFuncBody(A4Reporter rep, JoinableList<Err> errors, List<ErrorWarning> warns) throws Err {
        for (ArrayList<Func> entry : funcs.values())
            for (Func ff : entry) {
                Context cx = new Context(this, warns);
                cx.rootfunbody = ff;
                for (Decl d : ff.decls)
                    for (ExprHasName n : d.names)
                        cx.put(n.label, n);
                Expr newBody = cx.check(ff.getBody());
                if (ff.isPred)
                    newBody = newBody.resolve_as_formula(warns);
                else
                    newBody = newBody.resolve_as_set(warns);
                errors = errors.make(newBody.errors);
                if (!newBody.errors.isEmpty())
                    continue;
                try {
                    ff.setBody(newBody);
                } catch (Err er) {
                    errors = errors.make(er);
                    continue;
                }
                if (warns != null && ff.returnDecl.type().hasTuple() && newBody.type().hasTuple() && !newBody.type().intersects(ff.returnDecl.type()))
                    warns.add(new ErrorWarning(newBody.span(), "Function return value is disjoint from its return type.\n" + "Function body has type " + newBody.type() + "\n" + "but the return type is " + ff.returnDecl.type()));
                // else if (warns!=null && Version.experimental &&
                // !newBody.type.isSubtypeOf(ff.returnDecl.type))
                // warns.add(new ErrorWarning(newBody.span(),
                // "Function may return a tuple not in its declared return
                // type.\n"
                // +"The Alloy Analyzer's analysis may be unsound\n"
                // +"if it returns a tuple outside its declared return type.\n"
                // +"Function body has type "+newBody.type+"\nbut the return
                // type is "+ff.returnDecl.type));
                rep.typecheck(ff.toString() + ", BODY:" + newBody.type() + "\n");
            }
        return errors;
    }

    /**
     * Return an unmodifiable list of all functions in this module.
     */
    @Override
    public SafeList<Func> getAllFunc() {
        SafeList<Func> ans = new SafeList<Func>();
        for (ArrayList<Func> e : funcs.values())
            ans.addAll(e);
        return ans.dup();
    }

    // ============================================================================================================================//

    /** Add an ASSERT declaration. */
    String addAssertion(Pos pos, String name, Expr value) throws Err {
        status = 3;
        if (name == null || name.length() == 0)
            name = "assert$" + (1 + asserts.size());
        dup(pos, name, false);
        Expr old = asserts.put(name, ExprUnary.Op.NOOP.make(value.span().merge(pos), value));
        if (old != null) {
            asserts.put(name, old);
            throw new ErrorSyntax(pos, "\"" + name + "\" is already the name of an assertion in this module.");
        }
        return name;
    }

    /**
     * Each assertion name now points to a typechecked Expr rather than an
     * untypechecked Exp.
     */
    private JoinableList<Err> resolveAssertions(A4Reporter rep, JoinableList<Err> errors, List<ErrorWarning> warns) throws Err {
        Context cx = new Context(this, warns);
        for (Map.Entry<String,Expr> e : asserts.entrySet()) {
            Expr expr = e.getValue();
            expr = cx.check(expr).resolve_as_formula(warns);
            if (expr.errors.isEmpty()) {
                e.setValue(expr);
                rep.typecheck("Assertion " + e.getKey() + ": " + expr.type() + "\n");
            } else
                errors = errors.make(expr.errors);
        }
        return errors;
    }

    /**
     * Return an unmodifiable list of all assertions in this module.
     */
    @Override
    public ConstList<Pair<String,Expr>> getAllAssertions() {
        TempList<Pair<String,Expr>> ans = new TempList<Pair<String,Expr>>(asserts.size());
        for (Map.Entry<String,Expr> e : asserts.entrySet()) {
            ans.add(new Pair<String,Expr>(e.getKey(), e.getValue()));
        }
        return ans.makeConst();
    }

    // ============================================================================================================================//

    /** Add a FACT declaration. */
    void addFact(Pos pos, String name, Expr value) throws Err {
        status = 3;
        if (name == null || name.length() == 0)
            name = "fact$" + (1 + facts.size());
        facts.add(new Pair<String,Expr>(name, ExprUnary.Op.NOOP.make(value.span().merge(pos), value)));
    }

    /**
     * Each fact name now points to a typechecked Expr rather than an untypechecked
     * Exp; we'll also add the sig appended facts.
     */
    private JoinableList<Err> resolveFacts(CompModule res, A4Reporter rep, JoinableList<Err> errors, List<ErrorWarning> warns) throws Err {
        Context cx = new Context(this, warns);
        for (int i = 0; i < facts.size(); i++) {
            String name = facts.get(i).a;
            Expr expr = facts.get(i).b;
            Expr checked = cx.check(expr);
            expr = checked.resolve_as_formula(warns);
            if (expr.errors.isEmpty()) {
                facts.set(i, new Pair<String,Expr>(name, expr));
                rep.typecheck("Fact " + name + ": " + expr.type() + "\n");
            } else
                errors = errors.make(expr.errors);
        }
        for (Sig s : sigs.values()) {
            Expr f = res.old2appendedfacts.get(res.new2old.get(s));
            if (f == null)
                continue;
            if (f instanceof ExprConstant && ((ExprConstant) f).op == ExprConstant.Op.TRUE)
                continue;
            Expr formula;
            cx.rootsig = s;
            if (s.isOne == null) {
                cx.put("this", s.decl.get());
                formula = cx.check(f).resolve_as_formula(warns);
            } else {
                cx.put("this", s);
                formula = cx.check(f).resolve_as_formula(warns);
            }
            cx.remove("this");
            if (formula.errors.size() > 0)
                errors = errors.make(formula.errors);
            else {
                s.addFact(formula);
                rep.typecheck("Fact " + s + "$fact: " + formula.type() + "\n");
            }
        }
        return errors;
    }

    /**
     * Return an unmodifiable list of all facts in this module.
     */
    @Override
    public SafeList<Pair<String,Expr>> getAllFacts() {
        return (new SafeList<Pair<String,Expr>>(facts)).dup();
    }

    /**
     * Return the conjunction of all facts in this module and all reachable
     * submodules (not including field constraints, nor including sig appended
     * constraints)
     */
    @Override
    public Expr getAllReachableFacts() {
        ArrayList<Expr> facts = new ArrayList<Expr>();
        for (CompModule m : world.getAllReachableModules())
            for (Pair<String,Expr> f : m.facts)
                facts.add(f.b);
        if (facts.size() == 0)
            return ExprConstant.TRUE;
        else
            return ExprList.make(null, null, ExprList.Op.AND, facts);
    }

    // ============================================================================================================================//

    /** Add a COMMAND declaration. */
    void addCommand(boolean followUp, Pos pos, ExprVar name, boolean check, int overall, int bitwidth, int seq, int tmn, int tmx, int exp, List<CommandScope> scopes, ExprVar label) throws Err {
        if (followUp && !Version.experimental)
            throw new ErrorSyntax(pos, "Syntax error encountering => symbol.");
        if (label != null)
            pos = Pos.UNKNOWN.merge(pos).merge(label.pos);
        status = 3;
        if (name.label.length() == 0)
            throw new ErrorSyntax(pos, "Predicate/assertion name cannot be empty.");
        if (name.label.indexOf('@') >= 0)
            throw new ErrorSyntax(pos, "Predicate/assertion name cannot contain \'@\'");
        String labelName = (label == null || label.label.length() == 0) ? name.label : label.label;
        Command parent = followUp ? commands.get(commands.size() - 1) : null;
        Command newcommand = new Command(pos, name, labelName, check, overall, bitwidth, seq, tmn, tmx, exp, scopes, null, name, parent);
        if (parent != null)
            commands.set(commands.size() - 1, newcommand);
        else
            commands.add(newcommand);
    }

    /** Add a COMMAND declaration. */
    void addCommand(boolean followUp, Pos pos, Expr e, boolean check, int overall, int bitwidth, int seq, int tmn, int tmx, int expects, List<CommandScope> scopes, ExprVar label) throws Err {

        if (followUp && !Version.experimental)
            throw new ErrorSyntax(pos, "Syntax error encountering => symbol.");

        if (label != null)
            pos = Pos.UNKNOWN.merge(pos).merge(label.pos);

        status = 3;
        String n;
        if (check)
            n = addAssertion(pos, "check$" + (1 + commands.size()), e);
        else
            addFunc(e.span().merge(pos), Pos.UNKNOWN, n = "run$" + (1 + commands.size()), null, new ArrayList<Decl>(), null, e);
        String labelName = (label == null || label.label.length() == 0) ? n : label.label;
        Command parent = followUp ? commands.get(commands.size() - 1) : null;
        Command newcommand = new Command(e.span().merge(pos), e, labelName, check, overall, bitwidth, seq, tmn, tmx, expects, scopes, null, ExprVar.make(null, n), parent);
        if (parent != null)
            commands.set(commands.size() - 1, newcommand);
        else
            commands.add(newcommand);
    }

    public void addDefaultCommand() {
        if (commands.isEmpty()) {
            addFunc(Pos.UNKNOWN, Pos.UNKNOWN, "$$Default", null, new ArrayList<Decl>(), null, ExprConstant.TRUE);
            commands.add(new Command(Pos.UNKNOWN, ExprConstant.TRUE, "Default", false, 4, 4, 4, -1, -1, 1, null, null, ExprVar.make(null, "$$Default"), null));
        }
    }

    /** Resolve a particular command. */
    private Command resolveCommand(Command cmd, ConstList<Sig> exactSigs, Expr globalFacts) throws Err {
        Command parent = cmd.parent == null ? null : resolveCommand(cmd.parent, exactSigs, globalFacts);
        String cname = ((ExprVar) (cmd.formula)).label;
        Expr e;
        Clause declaringClause = null;
        if (cmd.check) {
            List<Object> m = getRawQS(2, cname); // We prefer assertion in the
                                                // topmost module
            if (m.size() == 0 && cname.indexOf('/') < 0)
                m = getRawNQS(this, 2, cname);
            if (m.size() > 1)
                unique(cmd.pos, cname, m);
            if (m.size() < 1)
                throw new ErrorSyntax(cmd.pos, "The assertion \"" + cname + "\" cannot be found.");

            Expr expr = (Expr) (m.get(0));
            e = expr.not();
        } else {
            List<Object> m = getRawQS(4, cname); // We prefer fun/pred in the
                                                // topmost module
            if (m.size() == 0 && cname.indexOf('/') < 0)
                m = getRawNQS(this, 4, cname);
            if (m.size() > 1)
                unique(cmd.pos, cname, m);
            if (m.size() < 1)
                throw new ErrorSyntax(cmd.pos, "The predicate/function \"" + cname + "\" cannot be found.");
            Func f = (Func) (m.get(0));
            declaringClause = f;
            e = f.getBody();
            if (!f.isPred)
                e = e.in(f.returnDecl);
            if (f.decls.size() > 0)
                e = ExprQt.Op.SOME.make(null, null, f.decls, e);
        }
        if (e == null)
            e = ExprConstant.TRUE;
        TempList<CommandScope> sc = new TempList<CommandScope>(cmd.scope.size());
        for (CommandScope et : cmd.scope) {
            Sig s = getRawSIG(et.sig.pos, et.sig.label);
            if (s == null)
                throw new ErrorSyntax(et.sig.pos, "The sig \"" + et.sig.label + "\" cannot be found.");
            if (!s.isTopLevel() && s.isVariable != null)
                throw new ErrorSyntax(cmd.pos, "Mutable sig " + et.sig + " is not top-level thus cannot have scopes assigned.");
            if (et.isExact && s.isVariable != null)
                throw new ErrorSyntax(cmd.pos, "Sig " + et.sig + " is variable thus scope cannot be exact.");
            sc.add(new CommandScope(null, s, et.isExact, et.startingScope, et.endingScope, et.increment));
        }

        if (cmd.nameExpr != null) {
            cmd.nameExpr.setReferenced(declaringClause);
        }
        return new Command(cmd.pos, cmd.nameExpr, cmd.label, cmd.check, cmd.overall, cmd.bitwidth, cmd.maxseq, cmd.minprefix, cmd.maxprefix, cmd.expects, sc.makeConst(), exactSigs, globalFacts.and(e), parent);

    }

    /** Each command now points to a typechecked Expr. */
    private void resolveCommands(Expr globalFacts) throws Err {
        ConstList<Sig> exactSigs = ConstList.make(world.exactSigs);
        for (int i = 0; i < commands.size(); i++) {
            Command cmd = commands.get(i);
            cmd = resolveCommand(cmd, exactSigs, globalFacts);
            commands.set(i, cmd);
        }
    }

    /**
     * Return an unmodifiable list of all commands in this module.
     */
    @Override
    public ConstList<Command> getAllCommands() {
        return ConstList.make(commands);
    }

    // ============================================================================================================================//

    /**
     * Returns true if exists some entry (a,b) in the map, such that b==value (using
     * object identity as the comparison)
     */
    private static <K, V> boolean isin(V value, Map<K,V> map) {
        for (V v : map.values())
            if (v == value)
                return true;
        return false;
    }

    // ============================================================================================================================//

    private static void resolveFieldDecl(CompModule res, final A4Reporter rep, final Sig s, final List<ErrorWarning> warns, boolean defined) throws Err {
        // When typechecking each field:
        // * it is allowed to refer to earlier fields in the same SIG or in any
        // visible ancestor sig
        // * it is allowed to refer to visible sigs
        // * it is NOT allowed to refer to any predicate or function
        // * it should NOT to refer to variable fields/sigs unless it is also variable [electrum]
        // * it should NOT to be defined in a variable sigs unless it is also variable [electrum]
        // For example, if A.als opens B.als, and B/SIGX extends A/SIGY,
        // then B/SIGX's fields cannot refer to A/SIGY, nor any fields in
        // A/SIGY)
        final List<Decl> oldDecls = res.old2fields.get(res.new2old.get(s));
        if (oldDecls == null)
            return;
        final CompModule m = res.sig2module.get(s);
        final Context cx = new Context(m, warns);
        final ExprHasName dup = Decl.findDuplicateName(oldDecls);
        if (dup != null)
            throw new ErrorSyntax(dup.span(), "sig \"" + s + "\" cannot have 2 fields named \"" + dup.label + "\"");
        for (final Decl d : oldDecls) {
            if (d.expr.mult() != ExprUnary.Op.EXACTLYOF) {
                if (defined)
                    continue;
            } else {
                if (!defined)
                    continue;
            }
            // The name "this" does matter, since the parser and the typechecker
            // both refer to it as "this"
            cx.rootfield = d;
            cx.rootsig = s;
            cx.put("this", s.decl.get());
            Expr bound = cx.check(d.expr).resolve_as_set(warns);
            cx.remove("this");
            String[] names = new String[d.names.size()];
            for (int i = 0; i < names.length; i++)
                names[i] = d.names.get(i).label;
            Field[] fields = s.addTrickyField(d.span(), d.isPrivate, d.disjoint, d.disjoint2, null, d.isVar, names, bound);
            final VisitQuery<Sig> q = new VisitQuery<Sig>() {

                @Override
                public final Sig visit(Sig x) {
                    if (x.isVariable != null)
                        return x;
                    else
                        return null;
                }
            };
            Sig qr = q.visitThis(bound);
            if (d.isVar == null && qr != null)
                warns.add(new ErrorWarning(d.span(), "Static field types with variable bound.\n" + "Field " + d.names.get(0) + " is static but " + qr.label + " is variable."));
            if (d.isVar == null && s.isVariable != null)
                warns.add(new ErrorWarning(d.span(), "Static field inside variable sig.\n" + "Field " + d.names.get(0) + " is static but " + s.label + " is variable."));
            for (Field f : fields) {
                rep.typecheck("Sig " + s + ", Field " + f.label + ": " + f.type() + "\n");
            }
        }
    }

    // ============================================================================================================================//

    private static void rejectNameClash(final List<CompModule> modules) throws Err {
        // The Alloy language forbids two overlapping sigs from having fields
        // with the same name.
        // In other words: if 2 fields have the same name, then their type's
        // first column must not intersect.
        final Map<String,List<Field>> fieldname2fields = new LinkedHashMap<String,List<Field>>();
        for (CompModule m : modules) {
            for (Sig sig : m.sigs.values()) {
                for (Field field : sig.getFields()) {
                    List<Field> peers = fieldname2fields.get(field.label);
                    if (peers == null) {
                        peers = new ArrayList<Field>();
                        fieldname2fields.put(field.label, peers);
                    }
                    for (Field field2 : peers)
                        if (field.type().firstColumnOverlaps(field2.type()))
                            throw new ErrorType(field.pos, "Two overlapping signatures cannot have\n" + "two fields with the same name \"" + field.label + "\":\n\n1) one is in sig \"" + field.sig + "\"\n" + field.pos + "\n\n2) the other is in sig \"" + field2.sig + "\"\n" + field2.pos);
                    peers.add(field);
                }
            }
        }
    }

    // ============================================================================================================================//

    private static void resolveMeta(final CompModule root) throws Err {
        // Now, add the meta sigs and fields if needed
        Map<Sig,PrimSig> sig2meta = new LinkedHashMap<Sig,PrimSig>();
        Map<Field,PrimSig> field2meta = new LinkedHashMap<Field,PrimSig>();
        boolean hasMetaSig = false, hasMetaField = false;
        root.new2old.put(root.metaSig, root.metaSig);
        root.sigs.put(base(root.metaSig), root.metaSig);
        root.new2old.put(root.metaField, root.metaField);
        root.sigs.put(base(root.metaField), root.metaField);
        for (CompModule m : root.allModules)
            for (Sig s : new ArrayList<Sig>(m.sigs.values()))
                if (m != root || (s != root.metaSig && s != root.metaField)) {
                    PrimSig ka = new PrimSig(s.label + "$", root.metaSig, Attr.ONE, PRIVATE.makenull(s.isPrivate), Attr.META);
                    sig2meta.put(s, ka);
                    ka.addDefinedField(Pos.UNKNOWN, null, Pos.UNKNOWN, "value", s);
                    m.new2old.put(ka, ka);
                    m.sigs.put(base(ka), ka);
                    hasMetaSig = true;
                    Expr allfields = ExprConstant.EMPTYNESS;
                    for (Field field : s.getFields()) {
                        Pos priv = field.isPrivate;
                        if (priv == null)
                            priv = s.isPrivate;
                        PrimSig kb = new PrimSig(s.label + "$" + field.label, root.metaField, Attr.ONE, PRIVATE.makenull(priv), Attr.META);
                        field2meta.put(field, kb);
                        m.new2old.put(kb, kb);
                        m.sigs.put(base(kb), kb);
                        hasMetaField = true;
                        kb.addDefinedField(Pos.UNKNOWN, null, Pos.UNKNOWN, "value", field);
                        if (allfields == ExprConstant.EMPTYNESS)
                            allfields = kb;
                        else
                            allfields = allfields.plus(kb);
                    }
                    ka.addDefinedField(Pos.UNKNOWN, null, Pos.UNKNOWN, "fields", allfields);
                }
        for (Map.Entry<Sig,PrimSig> e : sig2meta.entrySet()) {
            Expr expr = null;
            if ((e.getKey()) instanceof PrimSig) {
                PrimSig a = (PrimSig) (e.getKey());
                if (a.parent != null && a.parent != UNIV)
                    expr = sig2meta.get(a.parent);
            }
            e.getValue().addDefinedField(Pos.UNKNOWN, null, Pos.UNKNOWN, "parent", (expr == null ? ExprConstant.EMPTYNESS : expr));
        }
        for (Map.Entry<Sig,PrimSig> e : sig2meta.entrySet()) {
            Sig s = e.getKey();
            PrimSig s2 = e.getValue();
            Expr allfields = ExprConstant.EMPTYNESS;
            for (Field f : s.getFields()) {
                PrimSig metaF = field2meta.get(f);
                if (allfields == ExprConstant.EMPTYNESS)
                    allfields = metaF;
                else
                    allfields = allfields.plus(metaF);
            }
            if (s instanceof PrimSig)
                for (Sig c : (((PrimSig) s).descendents()))
                    for (Field f : c.getFields()) {
                        PrimSig metaF = field2meta.get(f);
                        if (allfields == ExprConstant.EMPTYNESS)
                            allfields = metaF;
                        else
                            allfields = allfields.plus(metaF);
                    }
            s2.addDefinedField(Pos.UNKNOWN, null, Pos.UNKNOWN, "subfields", allfields);
        }
        if (hasMetaSig == false)
            root.facts.add(new Pair<String,Expr>("sig$fact", root.metaSig.no().and(root.metaField.no())));
        else if (hasMetaField == false)
            root.facts.add(new Pair<String,Expr>("sig$fact", root.metaField.no()));
    }

    // ============================================================================================================================//

    /**
     * This method resolves the entire world; NOTE: if it throws an exception, it
     * may leave the world in an inconsistent state!
     */
    static CompModule resolveAll(final A4Reporter rep, final CompModule root) throws Err {
        final List<ErrorWarning> warns = new ArrayList<ErrorWarning>();
        for (CompModule m : root.getAllReachableModules())
            root.allModules.add(m);
        resolveParams(rep, root.allModules);
        resolveModules(rep, root.allModules);
        for (CompModule m : root.allModules)
            for (Sig s : m.sigs.values())
                root.sig2module.put(s, m);
        // Resolves SigAST -> Sig, and topologically sort the sigs into the
        // "sorted" array
        root.new2old.put(UNIV, UNIV);
        root.new2old.put(SIGINT, SIGINT);
        root.new2old.put(SEQIDX, SEQIDX);
        root.new2old.put(STRING, STRING);
        root.new2old.put(NONE, NONE);
        HashSet<Object> topo = new HashSet<Object>();
        for (CompModule m : root.allModules)
            for (Sig s : m.sigs.values())
                resolveSig(root, topo, s, warns); // [electrum] sigs may also throw warnings
        // Add the non-defined fields to the sigs in topologically sorted order
        // (since fields in subsigs are allowed to refer to parent's fields)
        for (Sig oldS : root.new2old.keySet())
            resolveFieldDecl(root, rep, oldS, warns, false);
        // Typecheck the function declarations
        JoinableList<Err> errors = new JoinableList<Err>();
        for (CompModule x : root.allModules)
            errors = x.resolveFuncDecls(rep, errors, warns);
        if (!errors.isEmpty())
            throw errors.pick();
        // Typecheck the defined fields
        for (Sig oldS : root.new2old.keySet())
            resolveFieldDecl(root, rep, oldS, warns, true);
        if (Version.experimental && root.seenDollar)
            resolveMeta(root);
        // Reject name clash
        rejectNameClash(root.allModules);
        // Typecheck the function bodies, assertions, and facts (which can refer
        // to function declarations)
        for (CompModule x : root.allModules) {
            errors = x.resolveFuncBody(rep, errors, warns);
            errors = x.resolveAssertions(rep, errors, warns);
            errors = x.resolveFacts(root, rep, errors, warns);
            // also, we can collect up all the exact sigs and add them to the
            // root module's list of exact sigs
            for (String n : x.exactParams) {
                Sig sig = x.params.get(n);
                if (sig != null) {
                    if (sig.isVariable != null)
                        errors = errors.make(new ErrorSyntax(root.opens.get(x.path).pos, "Module " + x.moduleName + " forces parameter to be exact but " + sig + " variable."));
                    root.exactSigs.add(sig);
                }
            }
        }
        if (!errors.isEmpty())
            throw errors.pick();
        // Typecheck the run/check commands (which can refer to function bodies
        // and assertions)
        root.resolveCommands(root.getAllReachableFacts());
        if (!errors.isEmpty())
            throw errors.pick();
        for (ErrorWarning w : warns)
            rep.warning(w);
        for (Sig s : root.exactSigs)
            rep.debug("Forced to be exact: " + s + "\n");
        return root;
    }

    // ============================================================================================================================//

    /**
     * Add a global expression; if the name already exists, it is removed first.
     */
    @Override
    public void addGlobal(String name, Expr value) {
        globals.put(name, value);
    }

    /**
     * Resolve the name based on the current context and this module.
     */
    private Expr populate(TempList<Expr> ch, TempList<String> re, Decl rootfield, Sig rootsig, boolean rootfunparam, Func rootfunbody, Pos pos, String fullname, Expr THIS) {
        // Return object can be Func(with > 0 arguments) or Expr
        final String name = (fullname.charAt(0) == '@') ? fullname.substring(1) : fullname;
        boolean fun = (rootsig != null && (rootfield == null || rootfield.expr.mult() == ExprUnary.Op.EXACTLYOF)) || (rootsig == null && !rootfunparam);
        if (name.equals("univ"))
            return ExprUnary.Op.NOOP.make(pos, UNIV);
        if (name.equals("Int"))
            return ExprUnary.Op.NOOP.make(pos, SIGINT);
        if (name.equals("seq/Int"))
            return ExprUnary.Op.NOOP.make(pos, SEQIDX);
        if (name.equals("String"))
            return ExprUnary.Op.NOOP.make(pos, STRING);
        if (name.equals("none"))
            return ExprUnary.Op.NOOP.make(pos, NONE);
        if (name.equals("iden"))
            return ExprConstant.Op.IDEN.make(pos, 0);
        if (name.equals("sig$") || name.equals("field$"))
            if (world != null) {
                Sig s = world.sigs.get(name);
                if (s != null)
                    return ExprUnary.Op.NOOP.make(pos, s);
            }
        final List<Object> ans = name.indexOf('/') >= 0 ? getRawQS(fun ? 5 : 1, name) : getRawNQS(this, fun ? 5 : 1, name);
        final Sig param = params.get(name);
        if (param != null && !ans.contains(param))
            ans.add(param);
        for (Object x : ans) {
            if (x instanceof Sig) {
                Sig y = (Sig) x;
                ch.add(ExprUnary.Op.NOOP.make(pos, y, null, 0));
                re.add("sig " + y.label);
            } else if (x instanceof Func) {
                Func f = (Func) x;
                int fn = f.count();
                int penalty = 0;
                if (resolution == 1 && fn > 0 && rootsig != null && THIS != null && THIS.type().hasArity(1) && f.get(0).type().intersects(THIS.type())) {
                    // If we're inside a sig, and there is a unary variable
                    // bound to "this",
                    // we should consider it as a possible FIRST ARGUMENT of a
                    // fun/pred call
                    ConstList<Expr> t = Util.asList(THIS);
                    ch.add(fn == 1 ? ExprCall.make(pos, null, f, t, 1 + penalty) : ExprBadCall.make(pos, null, f, t, 1 + penalty)); // penalty
                                                                                                                                   // of
                                                                                                                                   // 1
                    re.add((f.isPred ? "pred this." : "fun this.") + f.label);
                }
                if (resolution == 1) {
                    ch.add(fn == 0 ? ExprCall.make(pos, null, f, null, penalty) : ExprBadCall.make(pos, null, f, null, penalty));
                    re.add((f.isPred ? "pred " : "fun ") + f.label);
                }
                if (resolution == 2 && f != rootfunbody && THIS != null && fullname.charAt(0) != '@' && fn > 0 && f.get(0).type().intersects(THIS.type())) {
                    // If there is some value bound to "this", we should
                    // consider it as a possible FIRST ARGUMENT of a fun/pred
                    // call
                    ConstList<Expr> t = Util.asList(THIS);
                    ch.add(fn == 1 ? ExprCall.make(pos, null, f, t, 0) : ExprBadCall.make(pos, null, f, t, 0));
                    re.add((f.isPred ? "pred this." : "fun this.") + f.label);
                }
                if (resolution != 1) {
                    ch.add(fn == 0 ? ExprCall.make(pos, null, f, null, 0) : ExprBadCall.make(pos, null, f, null, 0));
                    re.add((f.isPred ? "pred " : "fun ") + f.label);
                }
            }
        }
        // Within a field decl
        // (1) Can refer to any visible sig/param (but you cannot call any
        // function or predicates)
        // (2) Can refer to field in this sig (defined earlier than you), and
        // fields in any visible ancestor sig
        // Within an appended facts
        // (1) Can refer to any visible sig/param/func/predicate
        // (2) Can refer to any visible field
        // Within a function paramDecl/returnDecl
        // (1) Cannot call
        // (2) But can refer to anything else visible.
        // All else: we can call, and can refer to anything visible.
        for (CompModule m : getAllNameableModules())
            for (Sig s : m.sigs.values())
                if (m == this || s.isPrivate == null)
                    for (Field f : s.getFields())
                        if (f.isMeta == null && (m == this || f.isPrivate == null) && f.label.equals(name))
                            if (resolution == 1) {
                                Expr x = null;
                                if (rootsig == null) {
                                    x = ExprUnary.Op.NOOP.make(pos, f, null, 0);
                                } else if (rootsig.isSameOrDescendentOf(f.sig)) {
                                    x = ExprUnary.Op.NOOP.make(pos, f, null, 0);
                                    if (fullname.charAt(0) != '@')
                                        x = THIS.join(x);
                                } else if (rootfield == null || rootfield.expr.mult() == ExprUnary.Op.EXACTLYOF) {
                                    x = ExprUnary.Op.NOOP.make(pos, f, null, 1);
                                } // penalty of 1
                                if (x != null) {
                                    ch.add(x);
                                    re.add("field " + f.sig.label + " <: " + f.label);
                                }
                            } else if (rootfield == null || rootsig.isSameOrDescendentOf(f.sig)) {
                                Expr x0 = ExprUnary.Op.NOOP.make(pos, f, null, 0);
                                if (resolution == 2 && THIS != null && fullname.charAt(0) != '@' && f.type().firstColumnOverlaps(THIS.type())) {
                                    ch.add(THIS.join(x0));
                                    re.add("field " + f.sig.label + " <: this." + f.label);
                                    if (rootsig != null)
                                        continue;
                                }
                                ch.add(x0);
                                re.add("field " + f.sig.label + " <: " + f.label);
                            }
        if (metaSig() != null && (rootsig == null || rootfield == null)) {
            SafeList<PrimSig> children = null;
            try {
                children = metaSig().children();
            } catch (Err err) {
                return null;
            } // exception NOT possible
            for (PrimSig s : children)
                for (Field f : s.getFields())
                    if (f.label.equals(name)) {
                        Expr x = ExprUnary.Op.NOOP.make(pos, f, null, 0);
                        ch.add(x);
                        re.add("field " + f.sig.label + " <: " + f.label);
                    }
        }
        if (metaField() != null && (rootsig == null || rootfield == null)) {
            SafeList<PrimSig> children = null;
            try {
                children = metaField().children();
            } catch (Err err) {
                return null;
            } // exception NOT possible
            for (PrimSig s : children)
                for (Field f : s.getFields())
                    if (f.label.equals(name)) {
                        Expr x = ExprUnary.Op.NOOP.make(pos, f, null, 0);
                        ch.add(x);
                        re.add("field " + f.sig.label + " <: " + f.label);
                    }
        }
        return null;
    }

    public Pos getGlobal(String key) {
        Pos result = getGlobalFromModule(this, key);
        if (result != null) {
            return result;
        }

        for (CompModule cm : allModules) {
            if (cm == this)
                continue;

            result = getGlobalFromModule(cm, key);
            if (result != null) {
                return result;
            }
        }
        return result;
    }

    Pos getGlobalFromModule(CompModule module, String key) {
        Sig sig = module.sigs.get(key);
        if (sig != null)
            return sig.pos;
        ArrayList<Func> arrayList = module.funcs.get(key);
        if (arrayList == null || arrayList.isEmpty())
            return null;

        return arrayList.get(0).pos;
    }

    public <T> T visitExpressions(VisitReturn<T> visitor) {
        sigs.values().forEach(s -> {
            s.accept(visitor);
            s.getFieldDecls().forEach(d -> {
                d.names.forEach(x -> x.accept(visitor));
                d.expr.accept(visitor);
            });
            s.getFacts().forEach(f -> f.accept(visitor));
        });

        funcs.values().forEach(funs -> {
            funs.forEach(fun -> {
                fun.getBody().accept(visitor);
                fun.decls.forEach(d -> {
                    d.expr.accept(visitor);
                    d.names.forEach(n -> n.accept(visitor));
                });
                fun.returnDecl.accept(visitor);
            });
        });
        facts.forEach(fact -> {
            fact.b.accept(visitor);
        });
        asserts.values().forEach(assrt -> {
            assrt.accept(visitor);
        });
        commands.forEach(cmd -> {
            if (cmd.nameExpr != null)
                cmd.nameExpr.accept(visitor);

            cmd.additionalExactScopes.forEach(sig -> sig.accept(visitor));
            cmd.formula.accept(visitor);
            cmd.scope.forEach(scope -> {
                scope.sig.accept(visitor);
            });
        });
        opens.values().forEach(open -> {
            if (open.expressions != null)
                open.expressions.stream().filter(x -> x != null).forEach(ex -> ex.accept(visitor));
        });
        macros.values().forEach(macro -> {
            macro.accept(visitor);
        });
        params.values().forEach(x -> x.accept(visitor));
        return null;
    }

    public Expr find(Pos pos) {
        if (pos == null)
            return null;

        class Holder {

            int  width = Integer.MAX_VALUE;
            Expr expr;
        }
        Holder holder = new Holder();

        visitExpressions(new VisitQueryOnce<Object>() {

            @Override
            public boolean visited(Expr expr) {
                boolean visited = super.visited(expr);
                if (visited)
                    return visited;

                if (expr.pos == null || expr.pos == Pos.UNKNOWN)
                    return visited;

                if (expr.pos != null && expr.pos.contains(pos)) {

                    int width = expr.pos.width();
                    if (width <= holder.width) {
                        if (holder.expr == null || holder.expr.referenced() == null || expr.referenced() != null) {
                            holder.width = width;
                            holder.expr = expr;
                        }
                    }
                }
                return visited;
            }
        });

        return holder.expr;
    }

    @Override
    public String explain() {
        return "module " + moduleName;
    }

}
