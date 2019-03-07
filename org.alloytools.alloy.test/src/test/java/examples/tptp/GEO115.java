/**
 *
 */
package examples.tptp;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Variable;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;

/**
 * KK encoding of GEO115+1.p from http://www.cs.miami.edu/~tptp/
 *
 * @author Emina Torlak
 */
public final class GEO115 extends GEO159 {

    /**
     * Constructs a new instance of GEO115.
     */
    public GEO115() {
        super();
        // TODO Auto-generated constructor stub
    }

    /**
     * Returns the conjecture theorem_3_8_5.
     *
     * @return theorem_3_8_5
     */
    public final Formula theorem385() {
        // all c: curve, p, q, r: point |
        // c->p->q->r in between =>
        // incident.c - q in q.(p.(c.between)) + ((c.between).r).q
        final Variable c = Variable.unary("C");
        final Variable p = Variable.unary("P");
        final Variable q = Variable.unary("Q");
        final Variable r = Variable.unary("R");
        final Formula f0 = c.product(p).product(q).product(r).in(between);
        final Expression e0 = q.join(p.join(c.join(between)));
        final Expression e1 = c.join(between).join(r).join(q);
        final Formula f1 = incident.join(c).difference(q).in(e0.union(e1));
        return f0.implies(f1).forAll(p.oneOf(point).and(q.oneOf(point)).and(r.oneOf(point)).and(c.oneOf(curve)));
    }

    /**
     * Returns the conjunction of the axioms and the negation of the hypothesis.
     *
     * @return axioms() && !theorem385()
     */
    public final Formula checkTheorem385() {
        return axioms().and(theorem385().not());
    }

    private static void usage() {
        System.out.println("java examples.tptp.GEO115 [# curves] [# points]");
        System.exit(1);
    }

    /**
     * Usage: ava examples.tptp.GEO115 [scope]
     */
    public static void main(String[] args) {
        if (args.length < 1)
            usage();

        try {
            final int n = Integer.parseInt(args[0]);

            final Solver solver = new Solver();
            solver.options().setSolver(SATFactory.MiniSat);

            final GEO115 model = new GEO115();
            final Formula f = model.theorem385();

            final Bounds b = model.bounds(n);
            final Solution sol = solver.solve(f, b);

            System.out.println(sol);

        } catch (NumberFormatException nfe) {
            usage();
        }
    }

}
