package kodkod.engine.hol;

import java.util.Collection;
import java.util.List;
import java.util.Set;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Node;
import kodkod.ast.QuantifiedFormula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.ast.operator.Quantifier;
import kodkod.ast.visitor.AbstractReplacer;
import kodkod.engine.config.Options;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.fol2sat.Translator;
import kodkod.engine.hol.HOL2ProcTranslator.Conversion;
import kodkod.engine.satlab.SATAbortedException;
import kodkod.engine.satlab.SATSolver;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.TupleSet;
import kodkod.util.ints.IntSet;
import kodkod.util.nodes.AnnotatedNode;

public abstract class HOLTranslationOld extends HOLTranslation {

    public static class FOL extends HOLTranslationOld {

        final AnnotatedNode<Formula>  annotated;
        final Translation.Incremental folTr;
        final FOL                     prev;

        public FOL(AnnotatedNode<Formula> annotated, Bounds bounds, Options options) {
            super(bounds, options);
            this.annotated = annotated;
            this.prev = null;
            // TODO: pass annotated instead, so that it doesn't have to
            // re-annotate again
            folTr = Translator.translateIncremental(annotated.node(), bounds, options);
        }

        private FOL(FOL prev, Incremental trNext) {
            super(trNext.bounds(), trNext.options());
            this.folTr = trNext;
            this.annotated = null;
            this.prev = prev;
        }

        @Override
        public final boolean isFirstOrder() {
            return true;
        }

        @Override
        public Formula formula() {
            return annotated.node();
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
        public HOLTranslation next(Formula formula, Bounds bounds) {
            Translator.translateIncremental(formula, bounds, folTr);
            return this;
        }

        @Override
        public HOLTranslation next() {
            Translator.translateNext(folTr);
            return this;
        }
    }

    public static class Some4All extends HOLTranslationOld {

        public final AnnotatedNode<Formula> annotated;
        public final Formula                converted;
        public final List<Conversion>       conversions;
        private HOLTranslation              convTr;

        public Some4All(AnnotatedNode<Formula> annotated, Formula converted, List<Conversion> conversions, Bounds bounds, Options options) {
            super(bounds, options);
            assert conversions.size() == 1 : "not implemented for multiple parallel higher-order quantifiers";
            this.annotated = annotated;
            this.converted = converted;
            this.conversions = conversions;
            this.convTr = Translator.translateHOL(converted, bounds, options);
            for (Conversion conv : conversions) {
                assert conv.origQF.quantifier() == Quantifier.ALL : "Non-universal quantifier converted for Some4All";
            }
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
            return convTr.interpret();
        }

        @Override
        public Formula formula() {
            return convTr.formula();
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
                // finding the next candidate
                while (convTr.cnf().solve()) {
                    Instance inst = convTr.interpret();
                    rep.holCandidateFound(Some4All.this, inst);

                    // TODO: rewrite check by replacing all skolems with
                    // concrete values from sol (maybe not necessary?)
                    QuantifiedFormula qf = conversions.get(0).origQF;
                    Formula checkFormula = qf.not();

                    // verifying candidate
                    Bounds pi = bounds.clone();
                    for (Relation r : pi.relations()) {
                        pi.boundExactly(r, inst.tuples(r));
                    }
                    rep.holVerifyingCandidate(Some4All.this, inst, checkFormula, pi);
                    Translation checkTr = Translator.translate(checkFormula, pi, options);
                    if (!checkTr.cnf().solve()) {
                        rep.holCandidateVerified(Some4All.this, inst);
                        return true;
                    } else {
                        Instance cex = checkTr.interpret();

                        Collection<Relation> holSkolems = inst.skolems();
                        holSkolems.removeAll(bounds.skolems());
                        assert holSkolems.size() == 1;
                        Relation sk = holSkolems.iterator().next();
                        TupleSet clqTuples = cex.tuples(sk.name());

                        final Variable v = qf.decls().get(0).variable();
                        final Expression cexExpr = pi.ts2expr(clqTuples);
                        Formula cexInst = qf.formula().accept(new AbstractReplacer(annotated.sharedNodes()) {

                            @Override
                            public Expression visit(Variable variable) {
                                if (variable == v)
                                    return cexExpr;
                                return super.visit(variable);
                            }
                        });
                        Formula inc = cexInst;
                        rep.holCandidateNotVerified(Some4All.this, inst, cex);
                        rep.holFindingNextCandidate(Some4All.this, inc);
                        convTr = convTr.next(inc);
                    }
                }
                return false;
            }

            @Override
            public boolean solve() throws SATAbortedException {
                rep.holLoopStart(Some4All.this, convTr.formula(), convTr.bounds());
                return solveNext();
            }
        }
    }

    protected HOLTranslationOld(Bounds bounds, Options options) {
        super(bounds, options, 0);
    }

    @Override
    public boolean isFirstOrder() {
        return false;
    }

    @Override
    public Translation getCurrentFOLTranslation() {
        return null;
    }

    @Override
    public int numCandidates() {
        return 1;
    }

}
