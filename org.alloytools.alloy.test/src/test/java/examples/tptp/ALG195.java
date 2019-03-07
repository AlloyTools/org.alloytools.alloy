/**
 *
 */
package examples.tptp;

import static kodkod.ast.Formula.and;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;

/**
 * A KK encoding of ALG195+1.p from http://www.cs.miami.edu/~tptp/
 *
 * @author Emina Torlak
 */
public final class ALG195 extends Quasigroups7 {

    /**
     * Constructs a new instance of ALG195.
     */
    public ALG195() {}

    /**
     * Parametrization of axioms 12 and 13.
     *
     * @requires e's are unary, op is ternary
     */
    @Override
    Formula ax12and13(Relation[] e, Relation op) {
        return Formula.TRUE;
    }

    /**
     * Parametrization of axioms 14 and 15.
     *
     * @requires e's are unary, op is ternary
     */
    @Override
    Formula ax14and15(Relation[] e, Relation op) {
        final Expression expr0 = e[5].join(op); // op(e5,...)
        final Expression expr1 = e[5].join(expr0); // op(e5,e5)
        final Expression expr2 = expr1.join(expr0); // op(e5,op(e5,e5))
        final Expression expr3 = expr2.join(expr2.join(op)); // op(op(e5,op(e5,e5)),op(e5,op(e5,e5)))
        final Expression expr3a = expr3.join(op); // op(op(op(e5,op(e5,e5)),op(e5,op(e5,e5))),...)
        final Expression expr4 = e[5].join(expr3a); // op(op(op(e5,op(e5,e5)),op(e5,op(e5,e5))),e5)
        // e0 = op(op(op(e5,op(e5,e5)),op(e5,op(e5,e5))),op(e5,op(e5,e5)))
        final Formula f0 = e[0].eq(expr2.join(expr3a));
        // e2 = op(op(e5,op(e5,e5)),op(e5,op(e5,e5)))
        final Formula f2 = e[2].eq(expr3);
        // e3 = op(op(op(e5,op(e5,e5)),op(e5,op(e5,e5))),e5)
        final Formula f3 = e[3].eq(expr4);
        // e4 = op(e5,op(e5,e5))
        final Formula f4 = e[4].eq(expr2);
        // e6 =
        // op(op(op(op(e5,op(e5,e5)),op(e5,op(e5,e5))),e5),op(e5,op(e5,e5)))
        final Formula f6 = e[6].eq(expr2.join(expr4.join(op)));
        return and(f0, f2, f3, f4, f6);
    }

    /**
     * Parametrization of axioms 16-22.
     *
     * @requires e is unary, h is binary
     */
    @Override
    Formula ax16_22(Relation e, Relation h) {
        final Expression expr0 = e.join(op2); // op2(e,...)
        final Expression expr1 = e.join(expr0); // op2(e,e)
        final Expression expr2 = expr1.join(expr0); // op2(e,op2(e,e))
        final Expression expr3 = expr2.join(expr2.join(op2)); // op2(op2(e,op2(e,e)),op2(e,op2(e,e)))
        final Expression expr3a = expr3.join(op2); // op2(op2(op2(e,op2(e,e)),op2(e,op2(e,e))),...)
        final Expression expr4 = e.join(expr3a); // op2(op2(op2(e,op2(e,e)),op2(e,op2(e,e))),e)
        // h(e10) = op2(op2(op2(e,op2(e,e)),op2(e,op2(e,e))),op2(e,op2(e,e)))
        final Formula f0 = e1[0].join(h).eq(expr2.join(expr3a));
        // h(e11) = op2(e,e)
        final Formula f1 = e1[1].join(h).eq(expr1);
        // h(e12) = op2(op2(e,op2(e,e)),op2(e,op2(e,e)))
        final Formula f2 = e1[2].join(h).eq(expr3);
        // h(e13) = op2(op2(op2(e,op2(e,e)),op2(e,op2(e,e))),e)
        final Formula f3 = e1[3].join(h).eq(expr4);
        // h(e14) = op2(e,op2(e,e))
        final Formula f4 = e1[4].join(h).eq(expr2);
        // h(e16) =
        // op2(op2(op2(op2(e,op2(e,e)),op2(e,op2(e,e))),e),op2(e,op2(e,e)))
        final Formula f6 = e1[6].join(h).eq(expr2.join(expr4.join(op2)));

        return and(f0, f1, f2, f3, f4, f6);
    }

    /**
     * Returns the conjunction of the axioms and the negation of the hypothesis.
     *
     * @return axioms() && !co1()
     */
    public final Formula checkCO1() {
        return axioms().and(co1().not());
    }

    /**
     * Returns the bounds the problem (axioms 1, 4, 9-13, second formula of 14-15,
     * and first formula of 16-22).
     *
     * @return the bounds for the problem
     */
    @Override
    public final Bounds bounds() {
        final Bounds b = super.bounds();
        final TupleFactory f = b.universe().factory();

        final TupleSet op1h = b.upperBound(op1).clone();
        final TupleSet op2h = b.upperBound(op2).clone();

        for (int i = 0; i < 7; i++) {
            op1h.remove(f.tuple("e1" + i, "e1" + i, "e1" + i)); // axiom 12
            op2h.remove(f.tuple("e2" + i, "e2" + i, "e2" + i)); // axiom 13
        }

        final TupleSet op1l = f.setOf(f.tuple("e15", "e15", "e11")); // axiom
                                                                    // 14,
                                                                    // line
                                                                    // 2
        final TupleSet op2l = f.setOf(f.tuple("e25", "e25", "e21")); // axiom
                                                                    // 15,
                                                                    // line
                                                                    // 2

        op1h.removeAll(f.area(f.tuple("e15", "e15", "e10"), f.tuple("e15", "e15", "e16")));
        op1h.addAll(op1l);

        op2h.removeAll(f.area(f.tuple("e25", "e25", "e20"), f.tuple("e25", "e25", "e26")));
        op2h.addAll(op2l);

        b.bound(op1, op1l, op1h);
        b.bound(op2, op2l, op2h);

        final TupleSet high = f.area(f.tuple("e10", "e20"), f.tuple("e14", "e26"));
        high.addAll(f.area(f.tuple("e16", "e20"), f.tuple("e16", "e26")));

        // first line of axioms 16-22
        for (int i = 0; i < 7; i++) {
            Tuple t = f.tuple("e15", "e2" + i);
            high.add(t);
            b.bound(h[i], f.setOf(t), high);
            high.remove(t);
        }

        return b;
    }

    private static void usage() {
        System.out.println("java examples.tptp.ALG195");
        System.exit(1);
    }

    /**
     * Usage: java examples.tptp.ALG195
     */
    public static void main(String[] args) {

        try {

            final ALG195 model = new ALG195();
            final Solver solver = new Solver();
            solver.options().setSolver(SATFactory.MiniSat);
            final Formula f = model.checkCO1();
            final Bounds b = model.bounds();
            // System.out.println(model.decls());
            // System.out.println(model.ax2ax7());
            // System.out.println(b);
            final Solution sol = solver.solve(f, b);
            if (sol.instance() == null) {
                System.out.println(sol);
            } else {
                System.out.println(sol.stats());
                model.display(sol.instance());
            }
        } catch (NumberFormatException nfe) {
            usage();
        }
    }
}
