/**
 *
 */
package examples.tptp;

import static kodkod.ast.Expression.IDEN;
import static kodkod.ast.Expression.UNIV;

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
import kodkod.instance.Universe;

/**
 * A KK encoding of TOP020+1.p from http://www.cs.miami.edu/~tptp/
 *
 * @author Emina Torlak
 */
public final class TOP020 {

    private final Relation hausdorff;
    private final Relation member, open, disjoint, closed;
    private final Relation coerce, diagonal;
    private final Relation product, tsproduct, ordered;

    /**
     * Constructs a new instance of TOP020.
     */
    public TOP020() {
        hausdorff = Relation.unary("a_hausdorff_top_space");
        member = Relation.binary("a_member_of");
        open = Relation.binary("open_in");
        disjoint = Relation.binary("disjoint");
        closed = Relation.binary("closed_in");
        coerce = Relation.binary("coerce_to_class");
        diagonal = Relation.binary("the_diagonal_top");
        product = Relation.ternary("the_product_of");
        tsproduct = Relation.ternary("the_product_top_space_of");
        ordered = Relation.ternary("ordered_pair");
    }

    /**
     * Returns the_product_top_space_of[A][B].
     *
     * @return the_product_top_space_of[A][B]
     */
    final Expression the_product_top_space_of(Expression a, Expression b) {
        return b.join(a.join(tsproduct));
    }

    /**
     * Returns the_product_of[A][B].
     *
     * @return the_product_of[A][B]
     */
    final Expression the_product_of(Expression a, Expression b) {
        return b.join(a.join(product));
    }

    /**
     * Returns the_ordered_pair[A][B].
     *
     * @return the_ordered_pair[A][B]
     */
    final Expression the_ordered_pair(Expression a, Expression b) {
        return b.join(a.join(ordered));
    }

    /**
     * Returns coerce_to_class[A].
     *
     * @return coerce_to_class[A]
     */
    final Expression coerce_to_class(Expression a) {
        return a.join(coerce);
    }

    /**
     * Returns the_diagonal_top[A].
     *
     * @return the_diagonal_top[A]
     */
    final Expression the_diagonal_top(Expression a) {
        return a.join(diagonal);
    }

    /**
     * Returns a->b in a_member_of.
     *
     * @return a->b in a_member_of
     */
    final Formula a_member_of(Expression a, Expression b) {
        return a.product(b).in(member);
    }

    /**
     * Returns a->b in open_in.
     *
     * @return a->b in open_in
     */
    final Formula open_in(Expression a, Expression b) {
        return a.product(b).in(open);
    }

    /**
     * Returns a->b in closed_in.
     *
     * @return a->b in closed_in
     */
    final Formula closed_in(Expression a, Expression b) {
        return a.product(b).in(closed);
    }

    /**
     * Returns a->b in disjoint.
     *
     * @return a->b in disjoint
     */
    final Formula disjoint(Expression a, Expression b) {
        return a.product(b).in(disjoint);
    }

    /**
     * Returns the declarations.
     *
     * @return declarations
     */
    public final Formula decls() {

        final Variable a = Variable.unary("A");
        final Variable b = Variable.unary("B");

        final List<Formula> decls = new ArrayList<Formula>();
        decls.add(coerce.function(UNIV, UNIV));
        decls.add(diagonal.function(UNIV, UNIV));
        decls.add(the_product_top_space_of(a, b).one().forAll(a.oneOf(UNIV).and(b.oneOf(UNIV))));
        decls.add(the_product_of(a, b).one().forAll(a.oneOf(UNIV).and(b.oneOf(UNIV))));
        decls.add(the_ordered_pair(a, b).one().forAll(a.oneOf(UNIV).and(b.oneOf(UNIV))));

        return Formula.and(decls);
    }

    /**
     * Returns closed_subset_thm axiom.
     *
     * @return closed_subset_thm
     */
    public final Formula closed_subset_thm() {
        final Variable x = Variable.unary("X");
        final Variable a = Variable.unary("A");
        final Variable y = Variable.unary("Y");
        final Formula f0 = a_member_of(y, coerce_to_class(x)).and(a_member_of(y, a).not());
        final Formula f1 = y.join(member).intersection(open.join(x)).intersection(disjoint.join(a)).some();
        final Formula f2 = f0.implies(f1).forAll(y.oneOf(UNIV));
        return f2.implies(closed_in(a, x)).forAll(x.oneOf(UNIV).and(a.oneOf(UNIV)));
    }

    /**
     * Returns hausdorff axiom.
     *
     * @return hausdorff
     */
    public final Formula hausdorff() {
        final Variable x = Variable.unary("X");
        final Variable a = Variable.unary("A");
        final Variable b = Variable.unary("B");
        final Expression g1 = open.join(x).intersection(a.join(member));
        final Expression g2 = open.join(x).intersection(b.join(member));
        final Expression abrange = member.join(coerce_to_class(x));
        return a.eq(b).not().implies(g1.product(g2).intersection(disjoint).some()).forAll(a.oneOf(abrange).and(b.oneOf(abrange))).forAll(x.oneOf(hausdorff));
    }

    /**
     * Returns product_of_open_sets axiom.
     *
     * @return product_of_open_sets
     */
    public final Formula product_of_open_sets() {
        final Variable a = Variable.unary("A");
        final Variable x = Variable.unary("X");
        final Variable b = Variable.unary("B");
        final Variable y = Variable.unary("Y");
        final Formula f0 = open_in(a, x).and(open_in(b, y));
        final Formula f1 = open_in(the_product_of(a, b), the_product_top_space_of(x, y));
        return f0.implies(f1).forAll(a.oneOf(UNIV).and(x.oneOf(UNIV)).and(b.oneOf(UNIV)).and(y.oneOf(UNIV)));
    }

    /**
     * Returns product_top axiom.
     *
     * @return product_top
     */
    public final Formula product_top() {
        final Variable s = Variable.unary("S");
        final Variable t = Variable.unary("T");
        final Variable x = Variable.unary("X");
        final Formula f0 = a_member_of(x, coerce_to_class(the_product_top_space_of(s, t)));
        final Expression e0 = member.join(coerce_to_class(s));
        final Expression e1 = member.join(coerce_to_class(t));
        final Formula f1 = ordered.intersection(e0.product(e1).product(x)).some();
        return f0.implies(f1).forAll(s.oneOf(UNIV).and(t.oneOf(UNIV)).and(x.oneOf(UNIV)));
    }

    /**
     * Returns product axiom.
     *
     * @return product
     */
    public final Formula product() {
        final Variable x = Variable.unary("X");
        final Variable s = Variable.unary("S");
        final Variable t = Variable.unary("T");
        final Formula f0 = a_member_of(x, the_product_of(s, t));
        final Expression e0 = member.join(s);
        final Expression e1 = member.join(t);
        final Formula f1 = ordered.intersection(e0.product(e1).product(x)).some();
        return f0.iff(f1).forAll(x.oneOf(UNIV).and(s.oneOf(UNIV)).and(t.oneOf(UNIV)));
    }

    /**
     * Returns disjoint_defn axiom.
     *
     * @return disjoint_defn
     */
    public final Formula disjoint_defn() {
        final Variable a = Variable.unary("A");
        final Variable b = Variable.unary("B");
        return disjoint(a, b).iff(member.join(a).intersection(member.join(b)).no()).forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)));
    }

    /**
     * Returns ordered_pair axiom.
     *
     * @return ordered_pair
     */
    public final Formula ordered_pair() {
        final Variable a = Variable.unary("A");
        final Variable b = Variable.unary("B");
        final Variable c = Variable.unary("C");
        final Variable d = Variable.unary("D");
        final Formula f0 = the_ordered_pair(a, b).eq(the_ordered_pair(c, d));
        final Formula f1 = a.eq(c).and(b.eq(d));
        return f0.implies(f1).forAll(a.oneOf(UNIV).and(b.oneOf(UNIV)).and(c.oneOf(UNIV)).and(d.oneOf(UNIV)));
    }

    /**
     * Returns diagonal_top axiom.
     *
     * @return diagonal_top
     */
    public final Formula diagonal_top() {
        final Variable x = Variable.unary("X");
        final Variable s = Variable.unary("S");
        final Formula f0 = a_member_of(x, coerce_to_class(the_diagonal_top(s)));
        final Expression a = member.join(coerce_to_class(s));
        final Formula f1 = ordered.intersection((a.product(a).intersection(IDEN)).product(x)).some();
        return f0.iff(f1).forAll(x.oneOf(UNIV).and(s.oneOf(UNIV)));
    }

    /**
     * Returns the conjunction of all axioms.
     *
     * @return conjunction of all axioms.
     */
    public final Formula axioms() {
        return decls().and(closed_subset_thm()).and(hausdorff()).and(product_of_open_sets()).and(product_top()).and(product()).and(disjoint_defn()).and(ordered_pair()).and(diagonal_top());
    }

    /**
     * Returns challenge_AMR_1_4_4 conjecture.
     *
     * @return challenge_AMR_1_4_4
     */
    public final Formula challenge_AMR_1_4_4() {
        final Variable s = Variable.unary("S");
        return closed_in(coerce_to_class(the_diagonal_top(s)), the_product_top_space_of(s, s)).forAll(s.oneOf(hausdorff));
    }

    /**
     * Returns the conjunction of the axioms and the negation of the hypothesis.
     *
     * @return axioms() && !challenge_AMR_1_4_4()
     */
    public final Formula checkChallenge_AMR_1_4_4() {
        return axioms().and(challenge_AMR_1_4_4().not());
    }

    /**
     * Returns bounds for the given scope.
     *
     * @return bounds for the given scope.
     */
    public final Bounds bounds(int n) {
        assert n > 0;
        final List<String> atoms = new ArrayList<String>(n);
        for (int i = 0; i < n; i++)
            atoms.add("a" + i);
        final Universe u = new Universe(atoms);
        final Bounds b = new Bounds(u);
        final TupleFactory f = u.factory();
        b.bound(hausdorff, f.allOf(1));
        b.bound(member, f.allOf(2));
        b.bound(open, f.allOf(2));
        b.bound(disjoint, f.allOf(2));
        b.bound(closed, f.allOf(2));
        b.bound(coerce, f.allOf(2));
        b.bound(diagonal, f.allOf(2));
        b.bound(product, f.allOf(3));
        b.bound(tsproduct, f.allOf(3));
        b.bound(ordered, f.allOf(3));
        return b;
    }

    private static void usage() {
        System.out.println("java examples.tptp.TOP020 [univ size]");
        System.exit(1);
    }

    /**
     * Usage: java examples.tptp.TOP020 [univ size]
     */
    public static void main(String[] args) {
        if (args.length < 1)
            usage();

        try {
            final int n = Integer.parseInt(args[0]);
            if (n < 1)
                usage();
            final TOP020 model = new TOP020();
            final Solver solver = new Solver();
            solver.options().setSolver(SATFactory.MiniSat);
            final Formula f = model.checkChallenge_AMR_1_4_4();
            final Bounds b = model.bounds(n);
            // System.out.println(f);
            // System.out.println(b);
            final Solution sol = solver.solve(f, b);
            System.out.println(sol);
        } catch (NumberFormatException nfe) {
            usage();
        }
    }

}
