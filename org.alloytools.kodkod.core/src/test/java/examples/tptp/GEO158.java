package examples.tptp;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 * The GEO158+1 problem from http://www.cs.miami.edu/~tptp/
 *
 * @author Emina Torlak
 */
public class GEO158 {

    final Relation partOf, incident, sum, endPoint, innerPoint, meet, closed, open;
    final Relation curve, point;
    /*
     * part_of : C -> C incident_c : P -> C sum : C -> C -> one C end_point : P -> C
     * inner_point : P -> C meet : P -> C -> C closed : C open : C
     */

    /**
     * Constructs a new instance of GEO0040.
     */
    public GEO158() {
        super();
        partOf = Relation.binary("partOf");
        incident = Relation.binary("incident");
        sum = Relation.ternary("sum");
        endPoint = Relation.binary("endPoint");
        closed = Relation.unary("Closed");
        open = Relation.unary("Open");
        curve = Relation.unary("Curve");
        point = Relation.unary("Point");
        meet = Relation.ternary("meet");
        innerPoint = Relation.binary("innerPoint");
    }

    /**
     * Returns all the 'type' declarations.
     *
     * @return the type declarations
     */
    public Formula decls() {
        final Expression cc = curve.product(curve);
        final Expression pc = point.product(curve);
        final Formula f0 = partOf.in(cc);
        final Formula f1 = closed.in(curve).and(open.in(curve));
        final Formula f2 = meet.in(point.product(cc)).and(sum.in(curve.product(cc)));
        final Formula f3 = incident.in(pc).and(endPoint.in(pc)).and(innerPoint.in(pc));
        // all C1, C2: Curve | one C2.(C1.sum)
        final Variable c1 = Variable.unary("C1");
        final Variable c2 = Variable.unary("C2");
        final Formula f4 = c2.join(c1.join(sum)).one().forAll(c1.oneOf(curve).and(c2.oneOf(curve)));
        return f0.and(f1).and(f2).and(f3).and(f4);
    }

    /**
     * Returns the part_of_defn axiom.
     *
     * @return part_of_defn
     */
    public final Formula partOfDefn() {
        // all C, C1: Curve | C1->C in partOf iff incident.C1 in incident.C
        final Variable c = Variable.unary("C"), c1 = Variable.unary("C1");
        final Formula f = c1.product(c).in(partOf).iff(incident.join(c1).in(incident.join(c)));
        return f.forAll(c.oneOf(curve).and(c1.oneOf(curve)));
    }

    /**
     * Returns the sum_defn axiom.
     *
     * @return sum_defn
     */
    public final Formula sumDefn() {
        // all C, C1, C2: Curve | C1->C2->C in sum iff
        // incident.C = incident.C1 + incident.C2
        final Variable c1 = Variable.unary("C1");
        final Variable c2 = Variable.unary("C2");
        final Variable c = Variable.unary("C");
        final Formula f0 = c1.product(c2).product(c).in(sum);
        final Formula f1 = incident.join(c).eq(incident.join(c1).union(incident.join(c2)));
        return f0.iff(f1).forAll(c.oneOf(curve).and(c1.oneOf(curve)).and(c2.oneOf(curve)));
    }

    /**
     * Returns the end_point_defn axiom.
     *
     * @return end_point_defn
     */
    public final Formula endPointDefn() {
        /*
         * all P: Point, C: Curve | P->C in endPoint iff (P->C in incident && all C1,
         * C2: partOf.C & P.incident | C1->C2 in partOf || C2->C1 in partOf)
         */
        final Variable c = Variable.unary("C");
        final Variable p = Variable.unary("P");

        final Expression e0 = p.product(c);
        final Formula f0 = e0.in(endPoint);
        final Formula f1 = e0.in(incident);

        final Variable c1 = Variable.unary("C1"), c2 = Variable.unary("C2");
        final Formula f2 = c1.product(c2).in(partOf).or(c2.product(c1).in(partOf));
        final Expression e1 = partOf.join(c).intersection(p.join(incident));
        final Formula f3 = f2.forAll(c1.oneOf(e1).and(c2.oneOf(e1)));

        return f0.iff(f1.and(f3)).forAll(p.oneOf(point).and(c.oneOf(curve)));
    }

    /**
     * Returns the inner_point_defn axiom.
     *
     * @return inner_point_defn
     */
    public final Formula innerPointDefn() {
        // all P: Point, C: Curve | P->C in innerPoint iff
        // (P->C in incident && no P->C & endPoint)
        final Variable c = Variable.unary("C");
        final Variable p = Variable.unary("P");
        final Expression e0 = p.product(c);
        final Formula f0 = e0.in(innerPoint);
        final Formula f1 = e0.in(incident).and(e0.intersection(endPoint).no());
        return f0.iff(f1).forAll(p.oneOf(point).and(c.oneOf(curve)));
    }

    /**
     * Returns the meet_defn axiom.
     *
     * @return meet_defn
     */
    public final Formula meetDefn() {
        // all P: Point, C, C1: Curve | P->C->C1 in meet iff
        // (P->C in incident && P->C1 in incident &&
        // incident.C & incident.C1 in endPoint.C & endPoint.C1)
        final Variable c = Variable.unary("C");
        final Variable c1 = Variable.unary("C1");
        final Variable p = Variable.unary("P");

        final Formula f0 = p.product(c).product(c1).in(meet);
        final Formula f1 = p.product(c).in(incident).and(p.product(c1).in(incident));
        final Expression e0 = incident.join(c).intersection(incident.join(c1));
        final Expression e1 = endPoint.join(c).intersection(endPoint.join(c1));
        final Formula f2 = e0.in(e1);

        final Formula f3 = f0.iff(f1.and(f2));

        return f3.forAll(p.oneOf(point).and(c.oneOf(curve)).and(c1.oneOf(curve)));
    }

    /**
     * Returns the closed_defn axiom.
     *
     * @return closed_defn
     */
    public final Formula closedDefn() {
        // all C: Curve | C in Closed iff no endPoint.C
        final Variable c = Variable.unary("C");
        return c.in(closed).iff(endPoint.join(c).no()).forAll(c.oneOf(curve));
    }

    /**
     * Returns the open_defn axiom.
     *
     * @return open_defn
     */
    public final Formula openDefn() {
        // all C: Curve | C in Open iff some endPoint.C
        final Variable c = Variable.unary("C");
        return c.in(open).iff(endPoint.join(c).some()).forAll(c.oneOf(curve));
    }

    /**
     * Returns the c1 axiom.
     *
     * @return c1
     */
    public final Formula c1() {
        // all C, C1: Curve | (C1->C in partOf && C1 != C) => C1 in Open
        final Variable c = Variable.unary("C");
        final Variable c1 = Variable.unary("C1");
        final Formula f0 = c1.product(c).in(partOf).and(c1.eq(c).not());
        final Formula f1 = c1.in(open);
        return f0.implies(f1).forAll(c.oneOf(curve).and(c1.oneOf(curve)));
    }

    /**
     * Returns the c2 axiom.
     *
     * @return c2
     */
    public final Formula c2() {
        // all C, C1, C2, C3: Curve | ((C1 + C2 + C3)->C in partOf &&
        // some endPoint.C1 & endPoint.C2 & endPoint.C3) =>
        // (C2->C3 in partOf || C3->C2 in partOf || C1->C2 in partOf ||
        // C2->C1 in partOf || C1->C3 in partOf || C3->C1 in partOf)
        final Variable c = Variable.unary("C");
        final Variable c1 = Variable.unary("C1");
        final Variable c2 = Variable.unary("C2");
        final Variable c3 = Variable.unary("C3");

        final Formula f0 = c1.union(c2).union(c3).product(c).in(partOf);
        final Formula f1 = endPoint.join(c1).intersection(endPoint.join(c2)).intersection(endPoint.join(c3)).some();
        final Formula f2 = c2.product(c3).in(partOf).or(c3.product(c2).in(partOf));
        final Formula f3 = c1.product(c2).in(partOf).or(c2.product(c1).in(partOf));
        final Formula f4 = c1.product(c3).in(partOf).or(c3.product(c1).in(partOf));

        return f0.and(f1).implies(f2.or(f3).or(f4)).forAll(c.oneOf(curve).and(c1.oneOf(curve)).and(c2.oneOf(curve)).and(c3.oneOf(curve)));
    }

    /**
     * Returns the c3 axiom.
     *
     * @return c3
     */
    public final Formula c3() {
        // all C: Curve | some innerPoint.C
        final Variable c = Variable.unary("C");
        return innerPoint.join(c).some().forAll(c.oneOf(curve));
    }

    /**
     * Returns the c4 axiom.
     *
     * @return c4
     */
    public final Formula c4() {
        // all C: Curve, P: Point | P->C in innerPoint => some P.meet & sum.C
        final Variable c = Variable.unary("C");
        final Variable p = Variable.unary("P");
        final Formula f0 = p.product(c).in(innerPoint);
        final Formula f1 = p.join(meet).intersection(sum.join(c)).some();
        return f0.implies(f1).forAll(c.oneOf(curve).and(p.oneOf(point)));
    }

    /**
     * Returns the c5 axiom.
     *
     * @return c5
     */
    public final Formula c5() {
        // all C: Curve, P, Q, R: endPoint.C |
        // P = Q || P = R || Q = R
        final Variable c = Variable.unary("C");
        final Variable p = Variable.unary("P");
        final Variable q = Variable.unary("Q");
        final Variable r = Variable.unary("R");
        final Expression e0 = endPoint.join(c);
        final Formula f0 = p.eq(q).or(p.eq(r)).or(q.eq(r));
        return f0.forAll(c.oneOf(curve).and(p.oneOf(e0)).and(q.oneOf(e0)).and(r.oneOf(e0)));
    }

    /**
     * Returns the c6 axiom.
     *
     * @return c6
     */
    public final Formula c6() {
        // all C: Curve, P: endPoint.C | some endPoint.C - P
        final Variable c = Variable.unary("C");
        final Variable p = Variable.unary("P");
        final Expression e0 = endPoint.join(c);
        return e0.difference(p).some().forAll(c.oneOf(curve).and(p.oneOf(e0)));
    }

    /**
     * Returns the c7 axiom.
     *
     * @return c7
     */
    public final Formula c7() {
        // all C, C1, C2: Curve, P: Point | (C in Closed &&
        // P->C1->C2 in meet && sum[C1][C2] = C) =>
        // ((endPoint.C1)->C1->C2 in meet)
        final Variable c = Variable.unary("C");
        final Variable c1 = Variable.unary("C1");
        final Variable c2 = Variable.unary("C2");
        final Variable p = Variable.unary("P");

        final Formula f0 = c.in(closed).and(p.product(c1).product(c2).in(meet));
        final Formula f1 = c2.join(c1.join(sum)).eq(c);
        final Formula f2 = endPoint.join(c1).product(c1).product(c2).in(meet);
        return f0.and(f1).implies(f2).forAll(c.oneOf(curve).and(c1.oneOf(curve)).and(c2.oneOf(curve)).and(p.oneOf(point)));
    }

    /**
     * Returns the c8 axiom.
     *
     * @return c8
     */
    public final Formula c8() {
        // all C1, C2: Curve | some meet.C2.C1 => some sum[C1][C2]
        final Variable c1 = Variable.unary("C1");
        final Variable c2 = Variable.unary("C2");
        final Formula f0 = meet.join(c2).join(c1).some();
        final Formula f1 = c2.join(c1.join(sum)).some();
        return f0.implies(f1).forAll(c1.oneOf(curve).and(c2.oneOf(curve)));
    }

    /**
     * Returns the c9 axiom.
     *
     * @return c9
     */
    public final Formula c9() {
        // all C, C1: Curve | incident.C = incident.C1 => C = C1
        final Variable c = Variable.unary("C");
        final Variable c1 = Variable.unary("C1");
        return incident.join(c).eq(incident.join(c1)).implies(c.eq(c1)).forAll(c.oneOf(curve).and(c1.oneOf(curve)));
    }

    /**
     * Returns the conjunction of all axioms and decls
     *
     * @returns the conjunction of all axioms and decls
     */
    public Formula axioms() {
        return decls().and(partOfDefn()).and(sumDefn()).and(endPointDefn()).and(innerPointDefn()).and(meetDefn()).and(openDefn()).and(closedDefn()).and(c1()).and(c2()).and(c3()).and(c4()).and(c5()).and(c6()).and(c7()).and(c8()).and(c9());
    }

    /**
     * Returns the formula "some Curve"
     *
     * @return some Curve
     */
    public Formula someCurve() {
        return curve.some();
    }

    /**
     * Returns a bounds with the given number of maximum curves and points
     *
     * @return a bounds with the given number of maximum curves and points
     */
    public Bounds bounds(int scope) {
        assert scope > 0;
        List<String> atoms = new ArrayList<String>(scope);
        for (int i = 0; i < scope; i++)
            atoms.add("c" + i);
        for (int i = 0; i < scope; i++)
            atoms.add("p" + i);
        final Universe u = new Universe(atoms);
        final TupleFactory f = u.factory();
        final Bounds b = new Bounds(u);
        final TupleSet c = f.range(f.tuple("c0"), f.tuple("c" + (scope - 1)));
        final TupleSet p = f.range(f.tuple("p0"), f.tuple("p" + (scope - 1)));
        final TupleSet cc = c.product(c), pc = p.product(c);
        b.bound(curve, c);
        b.bound(point, p);
        b.bound(partOf, cc);
        b.bound(incident, pc);
        b.bound(sum, c.product(cc));
        b.bound(endPoint, pc);
        b.bound(innerPoint, pc);
        b.bound(meet, pc.product(c));
        b.bound(closed, c);
        b.bound(open, c);
        return b;
    }

    /**
     * Returns the conjunction of the axioms and the hypothesis.
     *
     * @return axioms() && someCurve()
     */
    public final Formula checkConsistent() {
        return axioms().and(someCurve());
    }

    private static void usage() {
        System.out.println("java examples.tptp.GEO158 [ univ size ]");
        System.exit(1);
    }

    /**
     * Usage: java examples.tptp.GEO158 [# univ size ]
     */
    public static void main(String[] args) {
        if (args.length < 1)
            usage();

        try {
            final int n = Integer.parseInt(args[0]);

            final Solver solver = new Solver();
            solver.options().setSolver(SATFactory.MiniSat);

            final GEO158 model = new GEO158();
            final Formula f = model.checkConsistent();

            // System.out.println(model.decls());
            // System.out.println(model.partOfDefn());
            // System.out.println(model.sumDefn());
            //
            // System.out.println(model.endPointDefn());
            // System.out.println(model.innerPointDefn());
            // System.out.println(model.meetDefn());
            //
            // System.out.println(model.openDefn());
            // System.out.println(model.closedDefn());
            // System.out.println(model.c1());
            //
            // System.out.println(model.c2());
            // System.out.println(model.c3());
            // System.out.println(model.c4());
            //
            // System.out.println(model.c6());
            // System.out.println(model.c7());
            // System.out.println(model.c8());
            //
            // System.out.println(model.c9());

            final Bounds b = model.bounds(n);
            final Solution sol = solver.solve(f, b);
            System.out.println(sol);
        } catch (NumberFormatException nfe) {
            usage();
        }
    }

}
