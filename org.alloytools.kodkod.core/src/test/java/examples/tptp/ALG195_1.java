/**
 *
 */
package examples.tptp;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 * @author emina
 */
public final class ALG195_1 {

    final Relation[] e1, e2, h;
    final Relation   op1, op2, s1, s2;

    /**
     * Constructs a new instance of Quasigroups7.
     */
    ALG195_1() {
        op1 = Relation.ternary("op1");
        op2 = Relation.ternary("op2");
        s1 = Relation.unary("s1");
        s2 = Relation.unary("s2");
        e1 = new Relation[7];
        e2 = new Relation[7];
        h = new Relation[7];
        for (int i = 0; i < 7; i++) {
            e1[i] = Relation.unary("e1" + i);
            e2[i] = Relation.unary("e2" + i);
            h[i] = Relation.binary("h" + (i + 1));
        }
    }

    private static Formula function(Relation s, Relation op) {
        final Variable x = Variable.unary("x"), y = Variable.unary("y");
        return y.join(x.join(op)).one().forAll(x.oneOf(s).and(y.oneOf(s)));
    }

    /**
     * Returns the relation constraints.
     *
     * @returns the relation constraints.
     */
    public final Formula decls() {
        Formula f = function(s1, op1).and(function(s2, op2));
        for (Relation x : h) {
            f = f.and(x.function(s1, s2));
        }
        for (int i = 0; i < 7; i++) {
            f = f.and(h[i].function(s1, s2));
            f = f.and(e1[i].one()).and(e2[i].one());
        }
        return f;
    }

    /**
     * States that op is a latin square over s = e[0] +...+ e[6].
     *
     * @requires e's are unary, s is unary, op is ternary
     */
    private static Formula opCoversRange(Relation[] e, Relation s, Relation op) {
        Formula f = Formula.TRUE;
        for (Relation x : e) {
            f = f.and(s.eq(s.join(x.join(op)))).and(s.eq(x.join(s.join(op))));
        }
        return f;
    }

    /**
     * Returns axioms 2 and 7.
     *
     * @return ax2 and ax7
     */
    public final Formula ax2ax7() {
        return opCoversRange(e1, s1, op1);
    }

    /**
     * Parametrization of axioms 3 and 6.
     *
     * @requires s is unary, op is ternary
     */
    private static Formula ax3and6(Relation[] e, Relation op) {
        Formula f = Formula.TRUE;
        for (Relation x : e) {
            for (Relation y : e) {
                Expression expr0 = x.join(y.join(op)); // op(y,x)
                Expression expr1 = y.join(expr0.join(op)); // op(op(y,x),y)
                Expression expr2 = y.join(expr1.join(op)); // op(op(op(y,x),y),y)
                f = f.and(expr2.eq(x));
            }
        }
        return f;
    }

    /**
     * Returns axiom 3.
     *
     * @return ax3
     */
    public final Formula ax3() {
        return ax3and6(e1, op1);
    }

    /**
     * Returns axioms 5 and 8.
     *
     * @return ax5 and ax8
     */
    public final Formula ax5ax8() {
        return opCoversRange(e2, s2, op2);
    }

    /**
     * Returns axiom 6.
     *
     * @return ax6
     */
    public final Formula ax6() {
        return ax3and6(e2, op2);
    }

    /**
     * Parametrization of axioms 12 and 13.
     *
     * @requires e's are unary, op is ternary
     */
    Formula ax12and13(Relation[] e, Relation op) {
        Formula f = Formula.TRUE;
        for (Relation r : e) {
            f = f.and(r.join(r.join(op)).eq(r).not());
        }
        return f;
    }

    /**
     * Returns axioms 9 and 10.
     *
     * @return axioms 9 and 10.
     */
    // public final Formula ax9ax10() {
    // Formula f = Formula.TRUE;
    // for(int i = 0 ; i < 6; i++) {
    // for(int j = i+1; j < 7; j++) {
    // f = f.and(e1[i].eq(e1[j]).not());
    // f = f.and(e2[i].eq(e2[j]).not());
    // }
    // }
    // return f;
    // }

    /**
     * Returns axiom 12.
     *
     * @return ax12
     */
    public final Formula ax12() {
        return ax12and13(e1, op1);
    }

    /**
     * Returns axiom 13.
     *
     * @return ax13
     */
    public final Formula ax13() {
        return ax12and13(e2, op2);
    }

    /**
     * Parametrization of axioms 14 and 15.
     *
     * @requires e's are unary, op is ternary
     */
    Formula ax14and15(Relation[] e, Relation op) {
        final Expression expr0 = e[5].join(op); // op(e5,...)
        final Expression expr1 = e[5].join(expr0); // op(e5,e5)
        final Expression expr2 = expr1.join(expr0); // op(e5,op(e5,e5))
        final Expression expr3 = expr2.join(expr2.join(op)); // op(op(e5,op(e5,e5)),op(e5,op(e5,e5)))
        final Expression expr3a = expr3.join(op); // op(op(op(e5,op(e5,e5)),op(e5,op(e5,e5))),...)
        final Expression expr4 = e[5].join(expr3a); // op(op(op(e5,op(e5,e5)),op(e5,op(e5,e5))),e5)
        // e0 = op(op(op(e5,op(e5,e5)),op(e5,op(e5,e5))),op(e5,op(e5,e5)))
        final Formula f0 = e[0].eq(expr2.join(expr3a));
        // e1 = op(e5,e5)
        final Formula f1 = e[1].eq(expr1);
        // e2 = op(op(e5,op(e5,e5)),op(e5,op(e5,e5)))
        final Formula f2 = e[2].eq(expr3);
        // e3 = op(op(op(e5,op(e5,e5)),op(e5,op(e5,e5))),e5)
        final Formula f3 = e[3].eq(expr4);
        // e4 = op(e5,op(e5,e5))
        final Formula f4 = e[4].eq(expr2);
        // e6 =
        // op(op(op(op(e5,op(e5,e5)),op(e5,op(e5,e5))),e5),op(e5,op(e5,e5)))
        final Formula f6 = e[6].eq(expr2.join(expr4.join(op)));
        return f0.and(f1).and(f2).and(f3).and(f4).and(f6);
    }

    /**
     * Returns lines 1 and 3-6 of axiom 14.
     *
     * @return ax14
     */
    public final Formula ax14() {
        return ax14and15(e1, op1);
    }

    /**
     * Returns lines 1 and 3-6 of axiom 15.
     *
     * @return ax15
     */
    public final Formula ax15() {
        return ax14and15(e2, op2);
    }

    /**
     * Parametrization of axioms 16-22.
     *
     * @requires e is unary, h is binary
     */
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
        // h1(e15) = e
        final Formula f5 = e1[5].join(h).eq(e);
        // h(e16) =
        // op2(op2(op2(op2(e,op2(e,e)),op2(e,op2(e,e))),e),op2(e,op2(e,e)))
        final Formula f6 = e1[6].join(h).eq(expr2.join(expr4.join(op2)));

        return f0.and(f1).and(f2).and(f3).and(f4).and(f5).and(f6);
    }

    /**
     * Returns axioms 16-22.
     *
     * @return axioms 16-22.
     */
    public final Formula ax16_22() {
        Formula f = Formula.TRUE;
        for (int i = 0; i < 7; i++) {
            f = f.and(ax16_22(e2[i], h[i]));
        }
        return f;
    }

    /**
     * Returns the conjunction of all axioms and implicit constraints (decls()).
     *
     * @return the conjunction of all axioms and implicit constraints
     */
    public final Formula axioms() {
        return decls().and(ax2ax7()).and(ax3()).and(ax5ax8()).and(ax6()).and(ax12()).and(ax13()).and(ax14()).and(ax15()).and(ax16_22());
    }

    /**
     * Returns the part of the conjecture 1 that applies to the given h.
     *
     * @return the part of the conjecture 1 that applies to the given h.
     */
    private final Formula co1h(Relation h) {
        Formula f = Formula.TRUE;
        for (Relation x : e1) {
            for (Relation y : e1) {
                Expression expr0 = (y.join(x.join(op1))).join(h); // h(op1(x,y))
                Expression expr1 = (y.join(h)).join((x.join(h)).join(op2)); // op2(h(x),h(y))
                f = f.and(expr0.eq(expr1));
            }
        }
        return f.and(s2.eq(s1.join(h)));
    }

    /**
     * Returns conjecture 1.
     *
     * @return co1
     */
    public final Formula co1() {

        Formula f = Formula.FALSE;
        for (int i = 0; i < 7; i++) {
            f = f.or(co1h(h[i]));
        }

        return f;
    }

    /**
     * Returns the partial bounds the problem (axioms 1, 4, 9-11).
     *
     * @return the partial bounds for the problem
     */
    public Bounds bounds() {
        final List<String> atoms = new ArrayList<String>(14);
        for (int i = 0; i < 7; i++)
            atoms.add("e1" + i);
        for (int i = 0; i < 7; i++)
            atoms.add("e2" + i);

        final Universe u = new Universe(atoms);
        final Bounds b = new Bounds(u);
        final TupleFactory f = u.factory();

        final TupleSet s1bound = f.range(f.tuple("e10"), f.tuple("e16"));
        final TupleSet s2bound = f.range(f.tuple("e20"), f.tuple("e26"));

        b.boundExactly(s1, s1bound);
        b.boundExactly(s2, s2bound);

        // axioms 9, 10, 11
        for (int i = 0; i < 7; i++) {
            b.boundExactly(e1[i], f.setOf("e1" + i));
            b.boundExactly(e2[i], f.setOf("e2" + i));
        }

        // axom 1
        b.bound(op1, f.area(f.tuple("e10", "e10", "e10"), f.tuple("e16", "e16", "e16")));
        // axiom 4
        b.bound(op2, f.area(f.tuple("e20", "e20", "e20"), f.tuple("e26", "e26", "e26")));

        final TupleSet hbound = s1bound.product(s2bound);
        for (Relation r : h) {
            b.bound(r, hbound);
        }

        return b;
    }

    private static void displayOp(Instance instance, Relation op) {
        System.out.println("\n" + op + ":");
        final Iterator<Tuple> iter = instance.tuples(op).iterator();
        for (int i = 0; i < 7; i++) {
            for (int j = 0; j < 7; j++) {
                System.out.print(iter.next().atom(2));
                System.out.print("\t");
            }
            System.out.println();
        }
    }

    /**
     * Prints the values of the op1, op2, and h1-h7 relations to standard out.
     */
    void display(Instance instance) {
        displayOp(instance, op1);
        displayOp(instance, op2);
        for (int i = 0; i < 7; i++) {
            System.out.println("\n" + h[i] + ":");
            System.out.println(instance.tuples(h[i]));
        }
    }

    private static void usage() {
        System.out.println("java examples.tptp.ALG195_1");
        System.exit(1);
    }

    /**
     * Usage: java examples.tptp.ALG195_1
     */
    public static void main(String[] args) {

        try {

            final ALG195_1 model = new ALG195_1();
            final Solver solver = new Solver();
            solver.options().setSolver(SATFactory.MiniSat);
            final Formula f = model.axioms().and(model.co1().not());
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
