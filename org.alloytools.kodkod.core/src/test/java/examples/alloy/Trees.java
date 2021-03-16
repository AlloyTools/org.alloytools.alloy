/**
 *
 */
package examples.alloy;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IntConstant;
import kodkod.ast.IntExpression;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.fol2sat.HigherOrderDeclException;
import kodkod.engine.fol2sat.UnboundLeafException;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.Universe;

/**
 * KK encoding of the Tree example from F. Zaraket, A. Aziz, and S. Khurshid's
 * "Sequential Encoding for Relational Analysis".
 *
 * @author Emina Torlak
 */
public final class Trees {

    /*
     * KK outperformed by the sequential analysis tool on this model
     */
    private final Relation V, E;

    /**
     * Constructs a new instance of the trees problem
     */
    public Trees() {
        V = Relation.unary("V");
        E = Relation.binary("E");
    }

    /**
     * Returns the declarations and facts of the model.
     *
     * @return
     *
     *         <pre>
     * sig V { E: set V }
     * fact UndirectedGraph { E = ~E }
     * fact NonEmpty { some V }
     *         </pre>
     */
    public final Formula declsAndFacts() {
        final Formula f0 = E.in(V.product(V));
        final Formula f1 = E.eq(E.transpose());
        final Formula f2 = V.some();
        return f0.and(f1).and(f2);
    }

    /**
     * Returns the inCycle predicate.
     *
     * @return
     *
     *         <pre>
     * pred InCycle(v: V, c: V -> V) {
     * v in v.c or
     * some v': v.c | v' in v.^(c - v->v' - v'->v)
     * }
     *         </pre>
     */
    public final Formula inCycle(Expression/* V */ v, Expression/* V->V */ c) {
        final Formula f0 = v.in(v.join(c));
        final Variable vp = Variable.unary("v'");
        final Formula f1 = vp.in(v.join((c.difference(v.product(vp)).difference(vp.product(v))).closure()));
        return f0.or(f1.forSome(vp.oneOf(v.join(c))));
    }

    /**
     * Returns the acyclic predicate.
     *
     * @return
     *
     *         <pre>
     * pred Acyclic() {
     *  not Cyclic(E)
     * }
     *         </pre>
     */
    public final Formula acyclic() {
        return cyclic(E).not();
    }

    /**
     * Returns the connected predicate.
     *
     * @return
     *
     *         <pre>
     * V->V in *c
     *         </pre>
     */
    public final Formula connected(Expression/* V->V */ c) {

        return V.product(V).in(c.reflexiveClosure());
    }

    /**
     * Returns statement 1.
     *
     * @return
     *
     *         <pre>
     * pred Statement1() { Connected(E) and Acyclic() }
     *         </pre>
     */
    public final Formula statement1() {
        return connected(E).and(acyclic());
    }

    /**
     * Returns statement 2.
     *
     * @return
     *
     *         <pre>
     * pred Statement2() {
     * Connected(E) and
     * all u: V | all v: u.E | not Connected( E - (u->v) - (v->u) )
     * }
     *         </pre>
     */
    public final Formula statement2() {
        final Variable u = Variable.unary("u");
        final Variable v = Variable.unary("v");
        final Formula f0 = connected(E);
        final Formula f1 = connected(E.difference(u.product(v)).difference(v.product(u))).not();
        final Formula f2 = f1.forAll(v.oneOf(u.join(E))).forAll(u.oneOf(V));
        return f0.and(f2);
    }

    /**
     * Returns statement 3.
     *
     * @return
     *
     *         <pre>
     * pred Statement3 () {
     * Connected(E) and #E = #V + #V - 2
     *         </pre>
     */
    public final Formula statement3() {
        final IntExpression vcount = V.count();
        return connected(E).and(E.count().eq(vcount.plus(vcount).minus(IntConstant.constant(2))));
    }

    /**
     * Returns statement 3.
     *
     * @return
     *
     *         <pre>
     * pred Statement4 () {
     * Acyclic() and #E = #V + #V - 2
     *         </pre>
     */
    public final Formula statement4() {
        final IntExpression vcount = V.count();
        return acyclic().and(E.count().eq(vcount.plus(vcount).minus(IntConstant.constant(2))));
    }

    /**
     * Returns the cyclic predicate.
     *
     * @return
     *
     *         <pre>
     * pred Cyclic(c: V->V) { some v: V | inCycle(v, c) }
     *         </pre>
     */
    public final Formula cyclic(Expression/* V->V */ c) {
        final Variable v = Variable.unary("v");
        return inCycle(v, c).forSome(v.oneOf(V));
    }

    /**
     * Returns statement 5.
     *
     * @return
     *
     *         <pre>
     * pred Statement5() {
     * Acyclic() and
     * all u,v: V | (u->v) not in E implies Cyclic(E + (u->v) + (v->u))
     * }
     *         </pre>
     */
    public final Formula statement5() {
        final Variable u = Variable.unary("u");
        final Variable v = Variable.unary("v");
        final Formula f0 = u.product(v).in(E).not().implies(cyclic(E.union(u.product(v).union(v.product(u)))));
        final Formula f1 = f0.forAll(u.oneOf(V).and(v.oneOf(V)));
        return acyclic().and(f1);
    }

    /**
     * Returns the EquivOfTreeDefns assertion.
     *
     * @return
     *
     *         <pre>
     * assert EquivOfTreeDefns {
     * Statement1() implies Statement2()
     * Statement2() implies Statement3()
     * Statement3() implies Statement4()
     * Statement4() implies Statement5()
     * Statement5() implies Statement1()
     * }
     *         </pre>
     */
    public final Formula equivOfTreeDefns() {
        final Formula s1 = statement1(), s2 = statement2(), s3 = statement3(), s4 = statement4(), s5 = statement5();
        final Formula f0 = s1.implies(s2);
        final Formula f1 = s2.implies(s3);
        final Formula f2 = s3.implies(s4);
        final Formula f3 = s4.implies(s5);
        final Formula f4 = s5.implies(s1);
        return f0.and(f1).and(f2).and(f3).and(f4);
    }

    /**
     * Returns the formula that checks the EquivOfTreeDefns assertion.
     *
     * @return declsAndFacts() and not equivOfTreeDefns()
     */
    public final Formula checkEquivOfTreeDefns() {
        return declsAndFacts().and(equivOfTreeDefns().not());
    }

    /**
     * Returns the bounds for the Trees problem that uses the given number of
     * vertices.
     *
     * @return bounds for the Trees problem that uses the given number of vertices
     */
    public final Bounds bounds(int n) {
        assert n > 0;
        final List<String> atoms = new ArrayList<String>(n);
        for (int i = 0; i < n; i++)
            atoms.add("v" + i);
        final Universe u = new Universe(atoms);
        final TupleFactory f = u.factory();
        final Bounds b = new Bounds(u);
        b.bound(V, f.allOf(1));
        b.bound(E, f.allOf(2));
        return b;
    }

    private static void usage() {
        System.out.println("java examples.Trees [# vertices]");
        System.exit(1);
    }

    /**
     * Usage: java examples.Trees [# vertices]
     */
    public static void main(String[] args) {
        if (args.length < 1)
            usage();
        try {
            final int n = Integer.parseInt(args[0]);
            final Trees model = new Trees();
            final Bounds b = model.bounds(n);

            final Solver solver = new Solver();
            solver.options().setSolver(SATFactory.MiniSat);
            solver.options().setBitwidth(16);
            // System.out.println(solver.solve(model.checkEquivOfTreeDefns(),
            // b));

            final Formula[] statements = new Formula[5];
            statements[0] = model.statement1();
            statements[1] = model.statement2();
            statements[2] = model.statement3();
            statements[3] = model.statement4();
            statements[4] = model.statement5();

            long time = 0;

            for (int i = 0; i < 5; i++) {
                Formula f = model.declsAndFacts().and(statements[i]).and(statements[(i + 1) % 5].not());
                Solution s = solver.solve(f, b);
                time += s.stats().translationTime() + s.stats().solvingTime();
                System.out.println(s);
                if (s.instance() != null) {
                    return;
                }
            }

            System.out.println("valid: " + time + " ms");

        } catch (NumberFormatException nfe) {
            usage();
        } catch (HigherOrderDeclException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (UnboundLeafException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }
}
