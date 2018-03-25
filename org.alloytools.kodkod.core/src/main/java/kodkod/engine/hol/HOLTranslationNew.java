package kodkod.engine.hol;

import static kodkod.engine.hol.Proc.foldPlus;
import static kodkod.engine.hol.Proc.map;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import kodkod.ast.Decl;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Node;
import kodkod.ast.QuantifiedFormula;
import kodkod.ast.Relation;
import kodkod.ast.UnaryExpression;
import kodkod.ast.Variable;
import kodkod.ast.operator.ExprOperator;
import kodkod.ast.visitor.AbstractReplacer;
import kodkod.engine.Evaluator;
import kodkod.engine.config.Options;
import kodkod.engine.fol2sat.FullNegationPropagator;
import kodkod.engine.fol2sat.HigherOrderDeclException;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.fol2sat.Translator;
import kodkod.engine.hol.Proc.Func1;
import kodkod.engine.satlab.SATAbortedException;
import kodkod.engine.satlab.SATSolver;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.TupleSet;
import kodkod.util.collections.Pair;
import kodkod.util.ints.IntSet;
import kodkod.util.nodes.AnnotatedNode;

public abstract class HOLTranslationNew extends HOLTranslation {

    /**
     * ========================================================================
     * Class HOLTranslationNew.FOL
     * ========================================================================
     */
    public static class FOL extends HOLTranslationNew {

        final Proc.FOL proc;
        final FOL      prev;
        Translation    folTr;

        public FOL(Proc.FOL proc, Options options, int depth) {
            super(proc.bounds(), options);
            this.proc = proc;
            this.prev = null;

            // TODO: pass annotated instead, so that it doesn't have to
            // re-annotate again
            folTr = options.solver().incremental() ? Translator.translateIncremental(proc.formula, bounds, options) : Translator.translate(proc.formula, bounds, options);
        }

        private FOL(FOL prev, Incremental trNext) {
            super(trNext.bounds(), trNext.options());
            this.proc = prev.proc;
            this.folTr = trNext;
            this.prev = prev;
        }

        @Override
        public final boolean isFirstOrder() {
            return true;
        }

        @Override
        public Formula formula() {
            return proc.formula;
        }

        @Override
        public Translation getCurrentFOLTranslation() {
            return folTr;
        }

        @Override
        public int numCandidates() {
            return 1;
        }

        @Override
        public IntSet primaryVariables(Relation relation) {
            return folTr.primaryVariables(relation);
        }

        @Override
        public int numPrimaryVariables() {
            return folTr.numPrimaryVariables();
        }

        @Override
        public SATSolver cnf() {
            return folTr.cnf();
        }

        @Override
        public HOLTranslation next(Formula formula, Bounds bnds) {
            if (folTr.options().solver().incremental()) {
                folTr = Translator.translateIncremental(formula, bnds, (Translation.Incremental) folTr);
                return this;
            } else {
                return HOLTranslator.translateHOL(formulaWithInc().and(formula), Proc.union(bounds(), bnds), options);
            }
        }

        @Override
        public HOLTranslationNew next() {
            Translator.translateNext(folTr);
            return this;
        }
    }

    /**
     * ========================================================================
     * Class HOLTranslationNew.Some4All
     * ========================================================================
     */
    public static class Some4All extends HOLTranslationNew {

        public final Proc.Some4All proc;
        private HOLTranslation     candTr;
        private int                numCandidates;

        public Some4All(Proc.Some4All proc, Options options, int depth) {
            super(proc.bounds(), options, depth);
            this.proc = proc;
            Proc ffp = proc.fullFlippedProc();
            this.candTr = ffp.translate(options, depth + 1);
            this.numCandidates = -1;
        }

        @Override
        public Formula formula() {
            return proc.formula();
        }

        public HOLTranslation convTr() {
            return candTr;
        }

        @Override
        public Translation getCurrentFOLTranslation() {
            return candTr.getCurrentFOLTranslation();
        }

        @Override
        public HOLTranslation next() {
            candTr = candTr.next();
            return this;
        }

        @Override
        public HOLTranslation next(Formula f, Bounds b) {
            candTr = candTr.next(f, b);
            return this;
        }

        @Override
        public int numCandidates() {
            return numCandidates;
        }

        // Translation methods -----------

        @Override
        public IntSet primaryVariables(Relation relation) {
            return candTr.primaryVariables(relation);
        }

        @Override
        public int numPrimaryVariables() {
            return candTr.numPrimaryVariables();
        }

        @Override
        public SATSolver cnf() {
            return new Solver();
        }

        @Override
        public Instance interpret() {
            return candTr.interpret(bounds);
        }

        // Replacer ----------------------

        class Replacer extends AbstractReplacer {

            protected Replacer(Set<Node> cached) {
                super(cached);
            }
        }

        // SATSolver methods -------------

        class Solver implements SATSolver {

            @Override
            public int numberOfVariables() {
                return candTr.cnf().numberOfVariables();
            }

            @Override
            public int numberOfClauses() {
                return candTr.cnf().numberOfClauses();
            }

            @Override
            public void addVariables(int numVars) {
                candTr.cnf().addVariables(numVars);
            }

            @Override
            public boolean addClause(int[] lits) {
                return candTr.cnf().addClause(lits);
            }

            @Override
            public boolean valueOf(int variable) {
                return candTr.cnf().valueOf(variable);
            }

            @Override
            public void free() {
                candTr.cnf().free();
            }

            public boolean solveNext() {
                // finding the next candidate
                int iterCnt = 0;
                int maxIter = options.getHolSome4AllMaxIter();
                while (candTr.cnf().solve()) {
                    iterCnt++;
                    Instance cand = candTr.interpret();
                    rep.holCandidateFound(Some4All.this, cand);

                    Formula checkFormula = Formula.and(proc.qpFormulas()).not();

                    // verifying candidate
                    Bounds pi = bounds.clone();
                    for (Relation r : pi.relations()) {
                        pi.boundExactly(r, cand.tuples(r));
                    }
                    rep.holVerifyingCandidate(Some4All.this, cand, checkFormula, pi);
                    Options opt = options.clone();
                    // opt.setOverflowPolicy(opt.overflowPolicy().dual);
                    HOLTranslation checkTr = HOLTranslator.translateHOL(checkFormula, pi, opt);
                    if (!checkTr.cnf().solve()) {
                        numCandidates = iterCnt;
                        rep.holCandidateVerified(Some4All.this, cand);
                        return true;
                    } else {
                        if (maxIter > 0 && iterCnt > maxIter)
                            throw new HOLException("[Some4All] Max number of iterations reached: " + maxIter);
                        Instance cex = checkTr.interpret();
                        rep.holCandidateNotVerified(Some4All.this, cand, cex);

                        Collection<Relation> holSkolems = cand.skolems();
                        holSkolems.removeAll(bounds.skolems());

                        List<Formula> cexInsts = new ArrayList<Formula>(proc.qpFormulas().length);
                        top: for (Formula f : proc.qpFormulas()) {
                            final Map<Variable,Expression> varmap = new HashMap<Variable,Expression>();
                            QuantifiedFormula qf = (QuantifiedFormula) f;
                            for (Decl d : qf.decls()) {
                                Relation sk = findSkolemRelation(holSkolems, d.variable());
                                TupleSet skTuples = cex.tuples(sk.name());
                                if (skTuples == null)
                                    continue top; // the cex does not involve
                                                 // this qf, so skip to next
                                varmap.put(d.variable(), pi.ts2expr(skTuples));
                            }
                            cexInsts.add(qf.formula().accept(new AbstractReplacer(new HashSet<Node>()) {

                                @Override
                                public Expression visit(Variable variable) {
                                    Expression expr = varmap.get(variable);
                                    if (expr == null)
                                        return super.visit(variable);
                                    if (expr == Expression.NONE)
                                        for (int i = 1; i < variable.arity(); i++)
                                            expr = expr.product(Expression.NONE);
                                    return expr;
                                }
                            }));
                        }
                        Formula fInc = Formula.and(cexInsts);
                        Bounds bInc = new Bounds(candTr.bounds().universe());
                        Proc x;
                        if (!options.isHolFullIncrements()) {
                            Bounds bCand = candTr.bounds();
                            x = HOLTranslator.toProc(fInc, bCand, options);
                            Pair<Formula,Bounds> p = x.firstOrderProblem();
                            Set<Relation> diff = new HashSet<Relation>(p.b.relations());
                            diff.removeAll(bCand.relations());
                            bInc = new Bounds(bCand.universe());
                            for (Relation r : diff) {
                                bInc.bound(r, p.b.lowerBound(r), p.b.upperBound(r));
                            }
                            fInc = p.a;
                        } else {
                            fInc = FullNegationPropagator.toNNF(AnnotatedNode.annotateRoots(fInc)).node();
                        }

                        rep.holFindingNextCandidate(Some4All.this, fInc);
                        try {
                            candTr = candTr.next(fInc, bInc);
                        } catch (HigherOrderDeclException e) {
                            candTr = HOLTranslator.translateHOL(candTr.formulaWithInc().and(fInc), candTr.bounds(), options);
                        }
                    }
                }
                numCandidates = iterCnt;
                return false;
            }

            @Override
            public boolean solve() throws SATAbortedException {
                rep.holLoopStart(Some4All.this, candTr.formula(), candTr.bounds());
                return solveNext();
            }
        }

        public Relation findSkolemRelation(Collection<Relation> holSkolems, Variable variable) {
            for (Relation r : holSkolems)
                if (r.getSkolemVar() == variable)
                    return r;
            assert false : "Skolem relation not found for variable " + variable;
            return null;
        }
    }

    /**
     * ========================================================================
     * Class HOLTranslationNew.Fixpoint
     * ========================================================================
     */
    public static class Fixpoint extends HOLTranslationNew {

        public final Proc.Fixpoint proc;
        private HOLTranslation     convTr;
        private Instance           convInst;
        private int                iterCnt;

        public Fixpoint(Proc.Fixpoint proc, Options options, int depth) {
            super(proc.bounds(), options, depth);
            this.proc = proc;
            this.convTr = proc.fullFlippedProc().translate(options, depth + 1);
        }

        @Override
        public Formula formula() {
            return proc.formula();
        }

        public HOLTranslation convTr() {
            return convTr;
        }

        @Override
        public Translation getCurrentFOLTranslation() {
            return convTr.getCurrentFOLTranslation();
        }

        @Override
        public HOLTranslation next() {
            convTr = convTr.next();
            return this;
        }

        @Override
        public HOLTranslation next(Formula f, Bounds b) {
            convTr = convTr.next(f, b);
            return this;
        }

        @Override
        public int numCandidates() {
            return iterCnt;
        }

        // Translation methods -----------

        @Override
        public IntSet primaryVariables(Relation relation) {
            return convTr.primaryVariables(relation);
        }

        @Override
        public int numPrimaryVariables() {
            return convTr.numPrimaryVariables();
        }

        @Override
        public SATSolver cnf() {
            return new Solver();
        }

        @Override
        public Instance interpret() {
            return convInst;
        }

        // Replacer ----------------------

        class Replacer extends AbstractReplacer {

            protected Replacer(Set<Node> cached) {
                super(cached);
            }
        }

        // SATSolver methods -------------

        class Solver implements SATSolver {

            @Override
            public int numberOfVariables() {
                return convTr.cnf().numberOfVariables();
            }

            @Override
            public int numberOfClauses() {
                return convTr.cnf().numberOfClauses();
            }

            @Override
            public void addVariables(int numVars) {
                convTr.cnf().addVariables(numVars);
            }

            @Override
            public boolean addClause(int[] lits) {
                return convTr.cnf().addClause(lits);
            }

            @Override
            public boolean valueOf(int variable) {
                return convTr.cnf().valueOf(variable);
            }

            @Override
            public void free() {
                convTr.cnf().free();
            }

            public boolean solveNext() {
                convInst = null;
                iterCnt = 0;
                int maxIter = options.getHolSome4AllMaxIter();
                HOLTranslation currTr = convTr;
                while (currTr.cnf().solve()) {
                    final Instance currInst = currTr.interpret();
                    final Evaluator eval = new Evaluator(currInst);
                    convTr = currTr;
                    convInst = currTr.interpret();
                    if (iterCnt == 0)
                        rep.holFixpointFirstSolution(Fixpoint.this, currInst);
                    else
                        rep.holFixpointIncrementingOutcome(Fixpoint.this, currInst);
                    if (maxIter > 0 && iterCnt > maxIter)
                        throw new HOLException("[Fixpoint] Max number of iterations reached: " + maxIter);
                    iterCnt++;
                    // TODO: works only when inc is first order
                    Formula inc = proc.fullConditionFormula().accept(new AbstractReplacer(new HashSet<Node>()) {

                        @Override
                        public Expression visit(UnaryExpression unaryExpr) {
                            if (unaryExpr.op() != ExprOperator.PRE)
                                return super.visit(unaryExpr);
                            TupleSet val = eval.evaluate(unaryExpr.expression());
                            return bounds.ts2expr(val);
                        }
                    });
                    // if (iterCnt == 1) {
                    // List<Formula> fix = new
                    // ArrayList<Formula>(bounds.relations().size());
                    // for (Relation r: bounds.relations()) {
                    // if (r.isAtom()) continue;
                    // if (!r.name().endsWith("_clq") &&
                    // !r.name().endsWith("_e")) {
                    // Expression val = bounds.ts2expr(currInst.tuples(r));
                    // fix.add(val == Expression.NONE ? r.no() : r.eq(val));
                    // }
                    // }
                    // inc = inc.and(Formula.and(fix));
                    // }
                    rep.holFixpointIncrementing(Fixpoint.this, inc);
                    currTr = currTr.next(inc);
                }
                if (convInst != null && iterCnt > 0)
                    rep.holFixpointIncrementingOutcome(Fixpoint.this, null);
                return convInst != null;
            }

            @Override
            public boolean solve() throws SATAbortedException {
                rep.holFixpointStart(Fixpoint.this, convTr.formula(), convTr.bounds());
                return solveNext();
            }
        }

        public Relation findSkolemRelation(Collection<Relation> holSkolems, Variable variable) {
            for (Relation r : holSkolems)
                if (r.getSkolemVar() == variable)
                    return r;
            assert false : "Skolem relation not found for variable " + variable;
            return null;
        }
    }

    /**
     * ========================================================================
     * Class HOLTranslationNew.ORSplit
     * ========================================================================
     */
    public static class OR extends HOLTranslationNew {

        public final Proc.OR           proc;
        private final HOLTranslation[] splitTransl;
        private HOLTranslation         solTr     = null;
        private int                    currTrIdx = 0;

        public OR(final Proc.OR proc, final Options options, final int depth) {
            super(Proc.union(map(proc.disjuncts, new Bounds[0], new Func1<Proc,Bounds>() {

                @Override
                public Bounds run(Proc a) {
                    return a.bounds;
                }
            })), options, depth);
            this.proc = proc;
            this.splitTransl = map(proc.disjuncts, new HOLTranslation[0], new Func1<Proc,HOLTranslation>() {

                @Override
                public HOLTranslation run(Proc a) {
                    return a.translate(options, depth + 1);
                }
            });
        }

        public HOLTranslation currTr() {
            return splitTransl[currTrIdx];
        }

        @Override
        public Formula formula() {
            return proc.formula();
        }

        @Override
        public Translation getCurrentFOLTranslation() {
            return currTr().getCurrentFOLTranslation();
        }

        @Override
        public HOLTranslation next() {
            splitTransl[currTrIdx] = currTr().next();
            return this;
        }

        @Override
        public HOLTranslation next(Formula f) {
            splitTransl[currTrIdx] = currTr().next(f);
            return this;
        }

        @Override
        public HOLTranslation next(Formula f, Bounds b) {
            splitTransl[currTrIdx] = currTr().next(f, b);
            return this;
        }

        @Override
        public int numCandidates() {
            return currTrIdx;
        }

        // Translation methods -----------

        @Override
        public IntSet primaryVariables(Relation relation) {
            return splitTransl[0].primaryVariables(relation);
        } // TODO enough?

        @Override
        public int numPrimaryVariables() {
            return foldPlus(splitTransl, new Func1<HOLTranslation,Integer>() {

                @Override
                public Integer run(HOLTranslation a) {
                    return a.numPrimaryVariables();
                }
            });
        }

        @Override
        public SATSolver cnf() {
            return new Solver();
        }

        @Override
        public Instance interpret() {
            assert solTr != null : "no solution was found";
            return solTr.interpret();
        }

        @Override
        public Instance interpret(Bounds bnds) {
            assert solTr != null : "no solution was found";
            return solTr.interpret(bnds);
        }

        // SATSolver methods -------------

        class Solver implements SATSolver {

            @Override
            public int numberOfVariables() {
                return currTr().cnf().numberOfVariables();
            }

            @Override
            public int numberOfClauses() {
                return currTr().cnf().numberOfClauses();
            }

            @Override
            public void addVariables(int numVars) {
                currTr().cnf().addVariables(numVars);
            }

            @Override
            public boolean addClause(int[] lits) {
                return currTr().cnf().addClause(lits);
            }

            @Override
            public boolean valueOf(int variable) {
                return currTr().cnf().valueOf(variable);
            }

            @Override
            public void free() {
                currTr().cnf().free();
            }

            public boolean solveNext() throws SATAbortedException {
                for (int i = currTrIdx; i < splitTransl.length; i++) {
                    currTrIdx = i;
                    HOLTranslation tr = currTr();
                    rep.holSplitChoice(OR.this, tr.formula(), tr.bounds());
                    if (tr.cnf().solve()) {
                        solTr = tr;
                        rep.holSplitChoiceSAT(OR.this, solTr.interpret());
                        return true;
                    } else {
                        rep.holSplitChoiceUNSAT(OR.this);
                    }
                    ;
                }
                solTr = null;
                return false;
            }

            @Override
            public boolean solve() throws SATAbortedException {
                rep.holSplitStart(OR.this, formula());
                currTrIdx = 0;
                return solveNext();
            }
        }
    }

    protected HOLTranslationNew(Bounds bounds, Options options) {
        this(bounds, options, 0);
    }

    protected HOLTranslationNew(Bounds bounds, Options options, int depth) {
        super(bounds, options, depth);
    }
}
