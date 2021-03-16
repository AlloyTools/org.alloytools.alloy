/**
 *
 */
package examples.tptp;

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
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 * A KK encoding of NUM374+1.p from http://www.cs.miami.edu/~tptp/
 *
 * @author Emina Torlak
 */
public final class NUM374 {

    private final Relation sum, product, exponent, n1;

    /**
     * Constructs a new instance of NUM374.
     */
    public NUM374() {
        n1 = Relation.unary("n1");
        sum = Relation.ternary("sum");
        product = Relation.ternary("product");
        exponent = Relation.ternary("exponent");
    }

    /**
     * Returns op[X][Y].
     *
     * @return op[X][Y]
     */
    final Expression apply(Relation op, Expression X, Expression Y) {
        return Y.join(X.join(op));
    }

    /**
     * Returns sum[X][Y].
     *
     * @return sum[X][Y]
     */
    final Expression sum(Expression X, Expression Y) {
        return Y.join(X.join(sum));
    }

    /**
     * Returns product[X][Y].
     *
     * @return product[X][Y]
     */
    final Expression product(Expression X, Expression Y) {
        return Y.join(X.join(product));
    }

    /**
     * Returns exponent[X][Y].
     *
     * @return exponent[X][Y]
     */
    final Expression exponent(Expression X, Expression Y) {
        return Y.join(X.join(exponent));
    }

    /**
     * Returns the declarations.
     *
     * @return declarations.
     */
    public final Formula decls() {
        final Formula f0 = n1.one();
        final Variable x = Variable.unary("X");
        final Variable y = Variable.unary("Y");
        final Formula f1 = sum(x, y).one().and(product(x, y).one()).and(exponent(x, y).one());
        return f0.and(f1.forAll(x.oneOf(UNIV).and(y.oneOf(UNIV))));
    }

    /**
     * Returns all X, Y: Num | op[X][Y] = op[Y][X]
     *
     * @return all X, Y: Num | op[X][Y] = op[Y][X]
     */
    final Formula symmetric(Relation op) {
        // all X, Y: Num | op[X][Y] = op[Y][X]
        final Variable x = Variable.unary("X");
        final Variable y = Variable.unary("Y");
        return apply(op, x, y).eq(apply(op, y, x)).forAll(x.oneOf(UNIV).and(y.oneOf(UNIV)));
    }

    /**
     * Returns all X, Y, Z: Num | op[X][op[Y][Z]] = op[op[X][Y]][Z]
     *
     * @return all X, Y, Z: Num | op[X][op[Y][Z]] = op[op[X][Y]][Z]
     */
    final Formula associative(Relation op) {
        // all X, Y, Z: Num | op[X][op[Y][Z]] = op[op[X][Y]][Z]
        final Variable x = Variable.unary("X");
        final Variable y = Variable.unary("Y");
        final Variable z = Variable.unary("Z");
        return apply(op, x, apply(op, y, z)).eq(apply(op, apply(op, x, y), z)).forAll(x.oneOf(UNIV).and(y.oneOf(UNIV)).and(z.oneOf(UNIV)));
    }

    /**
     * Returns the sum_symmetry axiom.
     *
     * @return sum_symmetry
     */
    public final Formula sumSymmetry() {
        return symmetric(sum);
    }

    /**
     * Returns the sum_associativity axiom.
     *
     * @return sum_associativity
     */
    public final Formula sumAssociativity() {
        return associative(sum);
    }

    /**
     * Returns the product_identity axiom.
     *
     * @return product_identity
     */
    public final Formula productIdentity() {
        // ! [X] : product(X,n1) = X
        final Variable x = Variable.unary("X");
        return product(x, n1).eq(x).forAll(x.oneOf(UNIV));
    }

    /**
     * Returns the product_symmetry axiom.
     *
     * @return product_symmetry
     */
    public final Formula productSymmetry() {
        return symmetric(product);
    }

    /**
     * Returns the product_associativity axiom.
     *
     * @return product_associativity
     */
    public final Formula productAssociativity() {
        return associative(product);
    }

    /**
     * Returns the sum_product_distribution axiom.
     *
     * @return sum_product_distribution
     */
    public final Formula sumProductDistribution() {
        // ! [X,Y,Z] : product(X,sum(Y,Z)) = sum(product(X,Y),product(X,Z)) )).
        final Variable x = Variable.unary("X");
        final Variable y = Variable.unary("Y");
        final Variable z = Variable.unary("Z");
        return product(x, sum(y, z)).eq(sum(product(x, y), product(x, z))).forAll(x.oneOf(UNIV).and(y.oneOf(UNIV)).and(z.oneOf(UNIV)));
    }

    /**
     * Returns the exponent_n1 axiom.
     *
     * @return exponent_n1
     */
    public final Formula exponentN1() {
        // ! [X] : exponent(n1,X) = n1
        final Variable x = Variable.unary("X");
        return exponent(n1, x).eq(n1).forAll(x.oneOf(UNIV));
    }

    /**
     * Returns the exponent_identity axiom.
     *
     * @return exponent_identity
     */
    public final Formula exponentIdentity() {
        // ! [X] : exponent(X,n1) = X
        final Variable x = Variable.unary("X");
        return exponent(x, n1).eq(x).forAll(x.oneOf(UNIV));
    }

    /**
     * Returns the exponent_sum_product axiom.
     *
     * @return exponent_sum_product
     */
    public final Formula exponentSumProduct() {
        // ! [X,Y,Z] : exponent(X,sum(Y,Z)) =
        // product(exponent(X,Y),exponent(X,Z))
        final Variable x = Variable.unary("X");
        final Variable y = Variable.unary("Y");
        final Variable z = Variable.unary("Z");
        return exponent(x, sum(y, z)).eq(product(exponent(x, y), exponent(x, z))).forAll(x.oneOf(UNIV).and(y.oneOf(UNIV)).and(z.oneOf(UNIV)));
    }

    /**
     * Returns the exponent_product_distribution axiom.
     *
     * @return exponent_product_distribution
     */
    public final Formula exponentProductDistribution() {
        // ! [X,Y,Z] : exponent(product(X,Y),Z) =
        // product(exponent(X,Z),exponent(Y,Z))
        final Variable x = Variable.unary("X");
        final Variable y = Variable.unary("Y");
        final Variable z = Variable.unary("Z");
        return exponent(product(x, y), z).eq(product(exponent(x, z), exponent(y, z))).forAll(x.oneOf(UNIV).and(y.oneOf(UNIV)).and(z.oneOf(UNIV)));
    }

    /**
     * Returns the exponent_exponent axiom.
     *
     * @return exponent_exponent
     */
    public final Formula exponentExponent() {
        // ! [X,Y,Z] : exponent(exponent(X,Y),Z) = exponent(X,product(Y,Z))
        final Variable x = Variable.unary("X");
        final Variable y = Variable.unary("Y");
        final Variable z = Variable.unary("Z");
        return exponent(exponent(x, y), z).eq(exponent(x, product(y, z))).forAll(x.oneOf(UNIV).and(y.oneOf(UNIV)).and(z.oneOf(UNIV)));
    }

    /**
     * Returns the conjuction of all axioms.
     *
     * @return axioms
     */
    public final Formula axioms() {
        return decls().and(sumSymmetry()).and(sumAssociativity()).and(productIdentity()).and(productSymmetry()).and(productAssociativity()).and(sumProductDistribution()).and(exponentN1()).and(exponentIdentity()).and(exponentSumProduct()).and(exponentProductDistribution()).and(exponentExponent());
    }

    /**
     * Returns the wilkie conjecture.
     *
     * @return wilkie
     */
    public final Formula wilkie() {
        // ! [C,P,Q,R,S,A,B] :
        // ( ( C = product(A,A)
        // & P = sum(n1,A)
        // & Q = sum(P,C)
        // & R = sum(n1,product(A,C))
        // & S = sum(sum(n1,C),product(C,C)) )
        // =>
        // product(exponent(sum(exponent(P,A),exponent(Q,A)),B),exponent(sum(exponent(R,B),exponent(S,B)),A))
        // =
        // product(exponent(sum(exponent(P,B),exponent(Q,B)),A),exponent(sum(exponent(R,A),exponent(S,A)),B))
        // ) )).
        final Variable c = Variable.unary("C");
        final Variable p = Variable.unary("P");
        final Variable q = Variable.unary("Q");
        final Variable r = Variable.unary("R");
        final Variable s = Variable.unary("S");
        final Variable a = Variable.unary("A");
        final Variable b = Variable.unary("B");
        final Formula f0 = c.eq(product(a, a));
        final Formula f1 = p.eq(sum(n1, a));
        final Formula f2 = q.eq(sum(p, c));
        final Formula f3 = r.eq(sum(n1, product(a, c)));
        final Formula f4 = s.eq(sum(sum(n1, c), product(c, c)));
        final Expression e0 = product(exponent(sum(exponent(p, a), exponent(q, a)), b), exponent(sum(exponent(r, b), exponent(s, b)), a));
        final Expression e1 = product(exponent(sum(exponent(p, b), exponent(q, b)), a), exponent(sum(exponent(r, a), exponent(s, a)), b));
        final Formula f5 = e0.eq(e1);
        return (f0.and(f1).and(f2).and(f3).and(f4)).implies(f5).forAll(c.oneOf(UNIV).and(p.oneOf(UNIV)).and(q.oneOf(UNIV)).and(r.oneOf(UNIV)).and(s.oneOf(UNIV)).and(a.oneOf(UNIV)).and(b.oneOf(UNIV)));
    }

    /**
     * Returns the conjunction of the axioms and the negation of the hypothesis.
     *
     * @return axioms() && !wilkie()
     */
    public final Formula checkWilkie() {
        return axioms().and(wilkie().not());
    }

    /**
     * Returns the bounds for the given scope.
     *
     * @return bounds for the given scope
     */
    public final Bounds bounds(int n) {
        assert n > 0;
        final List<String> atoms = new ArrayList<String>(n);
        for (int i = 0; i < n; i++)
            atoms.add("a" + i);
        final Universe u = new Universe(atoms);
        final Bounds b = new Bounds(u);
        final TupleFactory f = u.factory();
        final TupleSet all3 = f.allOf(3);
        b.bound(sum, all3);
        b.bound(product, all3);
        b.bound(exponent, all3);
        b.bound(n1, f.allOf(1));
        return b;
    }

    private static void usage() {
        System.out.println("java examples.tptp.NUM374 [univ size]");
        System.exit(1);
    }

    /**
     * Usage: java examples.tptp.NUM374 [univ size]
     */
    public static void main(String[] args) {
        if (args.length < 1)
            usage();

        try {
            final int n = Integer.parseInt(args[0]);
            if (n < 1)
                usage();
            final NUM374 model = new NUM374();
            final Solver solver = new Solver();
            solver.options().setSolver(SATFactory.MiniSat);
            solver.options().setSymmetryBreaking(n * n);
            final Formula f = model.checkWilkie();
            final Bounds b = model.bounds(n);
            System.out.println(f);
            final Solution sol = solver.solve(f, b);
            System.out.println(sol);
        } catch (NumberFormatException nfe) {
            usage();
        }
    }
}
