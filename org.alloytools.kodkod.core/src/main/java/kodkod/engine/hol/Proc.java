package kodkod.engine.hol;

import java.lang.reflect.Array;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import kodkod.ast.FixFormula;
import kodkod.ast.Formula;
import kodkod.ast.QuantifiedFormula;
import kodkod.ast.Relation;
import kodkod.ast.operator.FormulaOperator;
import kodkod.engine.config.Options;
import kodkod.instance.Bounds;
import kodkod.util.collections.Pair;

public abstract class Proc {

    public static class NotComposableException extends RuntimeException {

        private static final long    serialVersionUID = -5979093923236801175L;
        public final Proc            left, right;
        public final FormulaOperator op;

        public NotComposableException(FormulaOperator op, Proc left, Proc right) {
            this.op = op;
            this.left = left;
            this.right = right;
        }
    }

    static abstract class Func<R> {

        public abstract R run();
    }

    static abstract class Func1<A, R> {

        public abstract R run(A a);
    }

    static abstract class Func2<A, B, R> {

        public abstract R run(A a, B b);
    }

    @SuppressWarnings("unchecked" )
    static <A, R> R[] map(A[] arr, R[] ans, Func1<A,R> func) {
        ans = (R[]) Array.newInstance(ans.getClass().getComponentType(), arr.length);
        for (int i = 0; i < arr.length; i++)
            ans[i] = func.run(arr[i]);
        return ans;
    }

    static <A, R> R fold(A[] arr, R acc, Func2<R,A,R> func) {
        R ans = acc;
        for (int i = 0; i < arr.length; i++)
            ans = func.run(acc, arr[i]);
        return ans;
    }

    static <A> int foldPlus(A[] arr, Func1<A,Integer> func) {
        return foldPlus(arr, 0, func);
    }

    static <A> int foldPlus(A[] arr, int acc, Func1<A,Integer> func) {
        for (int i = 0; i < arr.length; i++)
            acc += func.run(arr[i]);
        return acc;
    }

    /**
     * ========================================================================
     * Class Proc.FOL
     * ========================================================================
     */
    public static final class FOL extends Proc {

        public final Formula formula;

        public FOL(final Bounds bounds, final Formula formula) {
            super(bounds);
            assert bounds != null;
            this.formula = formula;
        }

        @Override
        public String print(String indent) {
            return indent + "FOL(" + formula + ")";
        }

        @Override
        public Formula formula() {
            return formula;
        }

        @Override
        public Pair<Formula,Bounds> firstOrderProblem() {
            return new Pair<Formula,Bounds>(formula, bounds);
        }

        @Override
        public boolean isFirstOrder() {
            return true;
        }

        @Override
        public Proc compose(FormulaOperator op, Proc right) {
            switch (op) {
                case AND :
                    if (right instanceof FOL) {
                        return new FOL(superset(right), formula.and(((FOL) right).formula));
                    }
                    if (right instanceof OR) {
                        return new OR(composeAll(op, this, ((OR) right).disjuncts));
                    }
                    if (right instanceof AND) {
                        return ((AND) right).composeFormula(bounds, formula, op);
                    }
                    throw new NotComposableException(op, this, right);
                case OR :
                    // if (right instanceof FOL && isSameBounds(right)) { return
                    // new FOL(bounds, formula.or(((FOL)right).formula)); }
                    // if (right instanceof FOL) { return new
                    // FOL(superset(right), formula.or(((FOL)right).formula)); }
                    if (right instanceof OR) {
                        return new OR(composeAll(op, this, ((OR) right).disjuncts));
                    }
                    return new OR(this, right);
                default :
                    throw new IllegalStateException("Expected formula in NNF; got operator: " + op);
            }
        }
    }

    /**
     * ========================================================================
     * Class Proc.HOL
     * ========================================================================
     */
    public abstract static class HOL extends Proc {

        protected HOL(Bounds bounds) {
            super(bounds);
        }
    }

    /**
     * ========================================================================
     * Class Proc.ORSplit
     * ========================================================================
     */
    public static class OR extends HOL {

        public final Proc[] disjuncts;

        public OR(Proc... splits) {
            super(union(map(splits, new Bounds[0], new Func1<Proc,Bounds>() {

                @Override
                public Bounds run(Proc a) {
                    return a.bounds();
                }
            })));
            this.disjuncts = splits;
            return;
            // NOTE: not safe to merge FOLs, because stuff might have been
            // skolemized.
            // The caller can perform optimizations to create FOL instead of OR
            // when safe.
            // Proc mergedFOLs = null;
            // List<Proc> rest = new ArrayList<Proc>(splits.length);
            // for (Proc p : splits) {
            // if (p instanceof FOL && mergedFOLs == null)
            // mergedFOLs = p;
            // else if (p instanceof FOL && mergedFOLs.isSameBounds(p))
            // mergedFOLs.compose(FormulaOperator.OR, p);
            // else
            // rest.add(p);
            // }
            // if (mergedFOLs == null)
            // this.disjuncts = rest.toArray(new Proc[0]);
            // else
            // this.disjuncts = concat(new Proc[] { mergedFOLs },
            // rest.toArray(new Proc[0]));
        }

        @Override
        public boolean isFirstOrder() {
            return false;
        }

        @Override
        public Formula formula() {
            return Formula.or(map(disjuncts, new Formula[0], new Func1<Proc,Formula>() {

                @Override
                public Formula run(Proc p) {
                    return p.formula();
                }
            }));
        }

        @Override
        public Pair<Formula,Bounds> firstOrderProblem() {
            Formula[] formulas = new Formula[disjuncts.length];
            Bounds[] boundss = new Bounds[disjuncts.length];
            for (int i = 0; i < disjuncts.length; i++) {
                Pair<Formula,Bounds> p = disjuncts[i].firstOrderProblem();
                formulas[i] = p.a;
                boundss[i] = p.b;
            }
            return new Pair<Formula,Bounds>(Formula.or(formulas), union(boundss));
        }

        @Override
        public String print(String indent) {
            String ans = indent + "OR(\n";
            for (Proc split : disjuncts)
                ans += split.print(indent + "  ") + ", \n";
            ans += indent + ")";
            return ans;
        }

        @Override
        public Proc compose(FormulaOperator op, Proc right) {
            switch (op) {
                case AND :
                    if (right instanceof FOL)
                        return new OR(composeAll(op, disjuncts, right));
                    if (right instanceof OR)
                        return new OR(composeAll(op, disjuncts, ((OR) right).disjuncts));
                    if (right instanceof AND)
                        return new OR(composeAll(op, disjuncts, right)); // new
                                                                        // OR(concat(disjuncts,
                                                                        // new
                                                                        // Proc[]{right}));
                                                                        // ;//
                    throw new NotComposableException(op, this, right);
                case OR :
                    if (right instanceof FOL)
                        return new OR(concat(disjuncts, new Proc[] {
                                                                    right
                        }));
                    if (right instanceof OR)
                        return new OR(concat(disjuncts, ((OR) right).disjuncts));
                    if (right instanceof AND)
                        return new OR(concat(disjuncts, new Proc[] {
                                                                    right
                        }));
                    throw new NotComposableException(op, this, right);
                default :
                    throw new IllegalStateException("Expected formula in NNF; got operator: " + op);
            }
        }
    }

    /**
     * ========================================================================
     * Class Proc.AndHOL
     * ========================================================================
     */
    public static abstract class AND extends HOL {

        public static class QuantProc {

            public final Formula original;
            public final Formula flipped;
            public final Proc    proc;
            public final Proc    cond;

            public QuantProc(Formula formula, Formula flippedFormula, Proc body) {
                this(formula, flippedFormula, body, null);
            }

            public QuantProc(Formula formula, Formula flippedFormula, Proc body, Proc cond) {
                this.original = formula;
                this.flipped = flippedFormula;
                this.proc = body;
                this.cond = cond;
            }
        }

        public final Formula     conjuncts;
        public final QuantProc[] quantProcs;

        public AND(Bounds bounds, Formula conj, QuantProc... qp) {
            super(bounds);
            this.conjuncts = conj;
            this.quantProcs = qp;
        }

        @Override
        public boolean isFirstOrder() {
            return false;
        }

        @Override
        public Formula formula() {
            return fullFormula();
        }

        @Override
        public Pair<Formula,Bounds> firstOrderProblem() {
            Formula[] formulas = new Formula[quantProcs.length];
            Bounds[] boundss = new Bounds[quantProcs.length];
            for (int i = 0; i < quantProcs.length; i++) {
                Pair<Formula,Bounds> p = quantProcs[i].proc.firstOrderProblem();
                formulas[i] = p.a;
                boundss[i] = p.b;
            }
            return new Pair<Formula,Bounds>(Formula.and(formulas), union(boundss));
        }

        public Formula[] qpFormulas() {
            return cache("qpf", new Func<Formula[]>() {

                @Override
                public Formula[] run() {
                    return map(quantProcs, new Formula[0], new Func1<QuantProc,Formula>() {

                        @Override
                        public Formula run(QuantProc a) {
                            return a.original;
                        }
                    });
                }
            });
        }

        public Formula[] qpFlippedFormulas() {
            return cache("qpff", new Func<Formula[]>() {

                @Override
                public Formula[] run() {
                    return map(quantProcs, new Formula[0], new Func1<QuantProc,Formula>() {

                        @Override
                        public Formula run(QuantProc a) {
                            return a.flipped;
                        }
                    });
                }
            });
        }

        public Proc fullBodyProc() {
            return cache("fbp", new Func<Proc>() {

                @Override
                public Proc run() {
                    return foldCompose(FormulaOperator.AND, map(quantProcs, new Proc[0], new Func1<QuantProc,Proc>() {

                        @Override
                        public Proc run(QuantProc a) {
                            return a.proc;
                        }
                    }));
                }
            });
        }

        public Proc fullFlippedProc() {
            return cache("ffp", new Func<Proc>() {

                @Override
                public Proc run() {
                    Proc fbp = fullBodyProc();
                    return new FOL(bounds, conjuncts).compose(FormulaOperator.AND, fbp);
                }
            });
        }

        public Formula fullFormula() {
            return conjuncts.and(Formula.and(qpFormulas()));
        }

        public Formula fullFlippedFormula() {
            return conjuncts.and(Formula.and(qpFlippedFormulas()));
        }

        public <T extends AND> T composeFormula(Bounds leftBounds, Formula left, FormulaOperator op) {
            assert op == FormulaOperator.AND : "can only compose with AND";
            return make(superset(leftBounds), left.and(conjuncts), quantProcs);
        }

        public <T extends AND> T composeFormula(Bounds rightBounds, FormulaOperator op, Formula right) {
            assert op == FormulaOperator.AND : "can only compose with AND";
            return make(superset(rightBounds), conjuncts.and(right), quantProcs);
        }

        protected abstract <T extends AND> T make(Bounds b, Formula conj, QuantProc... qProcs);

        @Override
        public Proc compose(FormulaOperator op, Proc right) {
            switch (op) {
                case AND :
                    if (right instanceof FOL) {
                        return composeFormula(right.bounds, op, ((FOL) right).formula);
                    }
                    if (right instanceof OR) {
                        return new OR(composeAll(op, this, ((OR) right).disjuncts));
                    }
                    if (right instanceof AND) {
                        return make(superset(right), conjuncts.and(((AND) right).conjuncts), concat(quantProcs, ((AND) right).quantProcs));
                    }
                    throw new NotComposableException(op, this, right);
                case OR :
                    return new OR(this, right);
                default :
                    throw new IllegalStateException("Expected formula in NNF; got operator: " + op);
            }
        }

        @Override
        public String print(String indent) {
            String ans = indent + getClass().getSimpleName() + "(\n";
            ans += indent + "  " + conjuncts + ", \n";
            for (QuantProc qp : quantProcs)
                ans += qp.proc.print(indent + "   ") + ",\n";
            ans += indent + ")";
            return ans;
        }
    }

    /**
     * ========================================================================
     * Class Proc.Fixpoint
     * ========================================================================
     */
    public static class Fixpoint extends AND {

        public Fixpoint(Bounds bounds, FixFormula qf, Proc formProc, Proc condProc) {
            this(bounds, Formula.TRUE, new QuantProc(qf, qf.formula(), formProc, condProc));
        }

        public Fixpoint(Bounds bounds, Formula conjuncts, QuantProc... qProcs) {
            super(bounds, conjuncts, qProcs);
        }

        @SuppressWarnings("unchecked" )
        @Override
        protected Fixpoint make(Bounds b, Formula conj, QuantProc... qp) {
            return new Fixpoint(b, conj, qp);
        }

        public Formula[] qpConditionFormulas() {
            return cache("qpcf", new Func<Formula[]>() {

                @Override
                public Formula[] run() {
                    return map(quantProcs, new Formula[0], new Func1<QuantProc,Formula>() {

                        @Override
                        public Formula run(QuantProc a) {
                            return ((FixFormula) a.original).condition();
                        }
                    });
                }
            });
        }

        public Formula fullConditionFormula() {
            return Formula.and(qpConditionFormulas());
        }
    }

    /**
     * ========================================================================
     * Class Proc.Some4All
     * ========================================================================
     */
    public static class Some4All extends AND {

        public Some4All(Bounds bounds, QuantifiedFormula qf, Proc body) {
            this(bounds, Formula.TRUE, new QuantProc(qf, qf.body().quantify(qf.quantifier().opposite, qf.decls(), qf.domain()), body));
        }

        public Some4All(Bounds bounds, Formula conjuncts, QuantProc... qProcs) {
            super(bounds, conjuncts, qProcs);
        }

        @SuppressWarnings("unchecked" )
        @Override
        protected Some4All make(Bounds b, Formula conj, QuantProc... qp) {
            return new Some4All(b, conj, qp);
        }
    }

    // ========================================================================

    protected final Bounds           bounds;
    private final Map<String,Object> cache = new HashMap<String,Object>();

    protected Proc(Bounds bounds) {
        this.bounds = bounds;
    }

    // ---------------------------------------------------------------------------------------------
    // TODO: is it ok not to care about ints?
    // is it true that by construction all of these bounds will have the same
    // ints?
    protected boolean isSameBounds(Proc other) {
        if (bounds == other.bounds)
            return true;
        return bounds.relations().containsAll(other.bounds.relations());
    }

    protected Bounds sameBounds(Proc other) {
        assert isSameBounds(other) : "different bounds";
        return bounds;
    }

    protected Bounds pickGreater(Proc other) {
        if (bounds == other.bounds)
            return bounds;
        int n1 = bounds.relations().size();
        int n2 = other.bounds.relations().size();
        if (n1 == n2)
            return sameBounds(other);
        Bounds l, g;
        if (n1 < n2) {
            l = bounds;
            g = other.bounds;
        } else {
            l = other.bounds;
            g = bounds;
        }
        assert g.relations().containsAll(l.relations()) : "no superset for bounds";
        return g;
    }

    protected Bounds superset(Proc other) {
        return superset(other.bounds);
    }

    protected Bounds superset(Bounds other) {
        return Proc.union(this.bounds, other);
    }

    // ---------------------------------------------------------------------------------------------

    @SuppressWarnings("unchecked" )
    protected <V> V cache(String key, Func<V> func) {
        return (V) cache(cache, key, (Func<Object>) func);
    }

    protected <K, V> V cache(Map<K,V> cache, K key, Func<V> func) {
        V ans = cache.get(key);
        if (ans == null) {
            ans = func.run();
            cache.put(key, ans);
        }
        return ans;
    }

    public Bounds bounds() {
        return bounds.unmodifiableView();
    }

    public String print() {
        return print("");
    }

    public final HOLTranslation translate(Options options, int depth) {
        return HOLTranslator.proc2transl(this, options, depth);
    }

    public abstract boolean isFirstOrder();

    public abstract Formula formula();

    public abstract Pair<Formula,Bounds> firstOrderProblem();

    public abstract Proc compose(FormulaOperator op, Proc right);

    public abstract String print(String indent);

    @Override
    public String toString() {
        return print();
    }

    public static Proc[] composeAll(FormulaOperator op, Proc lhs, Proc[] rhss) {
        return composeAll(op, new Proc[] {
                                          lhs
        }, rhss);
    }

    public static Proc[] composeAll(FormulaOperator op, Proc[] lhss, Proc rhs) {
        return composeAll(op, lhss, new Proc[] {
                                                rhs
        });
    }

    public static Proc[] composeAll(FormulaOperator op, Proc[] lhss, Proc[] rhss) {
        Proc[] ans = new Proc[lhss.length * rhss.length];
        for (int i = 0; i < lhss.length; i++)
            for (int j = 0; j < rhss.length; j++)
                ans[i * rhss.length + j] = lhss[i].compose(op, rhss[j]);
        return ans;
    }

    public static Proc foldCompose(FormulaOperator op, Proc[] procs) {
        Proc ans = null;
        for (int i = 0; i < procs.length; i++)
            ans = ans == null ? procs[i] : ans.compose(op, procs[i]);
        return ans;
    }

    protected AND.QuantProc[] concat(AND.QuantProc[] a, AND.QuantProc[] b) {
        return concat(a, b, new AND.QuantProc[a.length + b.length]);
    }

    protected Proc[] concat(Proc[] a, Proc[] b) {
        return concat(a, b, new Proc[a.length + b.length]);
    }

    protected <T> T[] concat(T[] a, T[] b, T[] ans) {
        for (int i = 0; i < a.length; i++)
            ans[i] = a[i];
        for (int i = 0; i < b.length; i++)
            ans[a.length + i] = b[i];
        return ans;
    }

    public static Bounds union(Bounds b1, Bounds b2) {
        if (b1 == null)
            return b2;
        if (b2 == null)
            return b1;
        if (b1 == b2)
            return b1;
        if (b1.relations().containsAll(b2.relations()))
            return b1;
        if (b2.relations().containsAll(b1.relations()))
            return b2;
        Bounds ans = b1.clone();
        Set<Relation> diff = new HashSet<Relation>(b2.relations());
        // diff.removeAll(bounds.relations());
        for (Relation r : diff)
            ans.bound(r, b2.lowerBound(r), b2.upperBound(r));
        return ans;
    }

    public static Bounds union(Bounds[] bnds) {
        if (bnds == null || bnds.length == 0)
            return null;
        Bounds ans = bnds[0];
        for (int i = 1; i < bnds.length; i++)
            ans = union(ans, bnds[i]);
        return ans;
    }

}
