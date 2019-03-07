/*
 * Kodkod -- Copyright (c) 2005-2008, Emina Torlak
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package examples.alloy;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.ucore.AdaptiveRCEStrategy;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.Universe;
import kodkod.util.nodes.Nodes;

/**
 * A toy list specification.
 *
 * @author Emina Torlak
 */
public final class ToyLists {

    private final Relation list, nonEmptyList, emptyList, thing;
    private final Relation equivTo, prefixes, car, cdr;

    /**
     * Constructs a new instance of the toylists problem.
     */
    public ToyLists() {
        list = Relation.unary("List");
        nonEmptyList = Relation.unary("NonEmptyList");
        emptyList = Relation.unary("EmptyList");
        thing = Relation.unary("Thing");
        equivTo = Relation.binary("equivTo");
        prefixes = Relation.binary("prefixes");
        car = Relation.binary("car");
        cdr = Relation.binary("cdr");
    }

    private Expression car(Expression expr) {
        return expr.join(car);
    }

    private Expression cdr(Expression expr) {
        return expr.join(cdr);
    }

    private Expression equivTo(Expression expr) {
        return expr.join(equivTo);
    }

    private Expression prefixes(Expression expr) {
        return expr.join(prefixes);
    }

    private Formula equiv(Expression a, Expression b) {
        return a.in(equivTo(b));
    }

    private Formula prefix(Expression a, Expression b) {
        return a.in(prefixes(b));
    }

    /**
     * Returns the toylists spec.
     *
     * @return toylists spec
     */
    public Formula spec() {
        final Variable a = Variable.unary("a"), b = Variable.unary("b"), e = Variable.unary("e");

        final List<Formula> spec = new ArrayList<Formula>();
        spec.add(list.eq(nonEmptyList.union(emptyList)));
        spec.add(nonEmptyList.intersection(emptyList).no());

        spec.add(car.in(nonEmptyList.product(thing)));
        spec.add(car(a).one().forAll(a.oneOf(nonEmptyList)));

        spec.add(cdr.in(nonEmptyList.product(list)));
        spec.add(cdr(a).one().forAll(a.oneOf(nonEmptyList)));
        spec.add(e.in(a.join(cdr.reflexiveClosure())).forSome(e.oneOf(emptyList)).forAll(a.oneOf(list)));

        spec.add(equivTo.in(list.product(list)));
        spec.add(equiv(a, b).iff(car(a).eq(car(b)).and(equivTo(cdr(a)).eq(equivTo(cdr(b))))).forAll(a.oneOf(list).and(b.oneOf(list))));

        spec.add(prefixes.in(list.product(list)));
        spec.add(prefix(e, a).forAll(e.oneOf(emptyList).and(a.oneOf(list))));
        spec.add(prefix(a, e).not().forAll(e.oneOf(emptyList).and(a.oneOf(nonEmptyList))));

        spec.add(prefix(a, b).iff(car(a).eq(car(b)).and(prefix(cdr(a), cdr(b)))).forAll(a.oneOf(nonEmptyList).and(b.oneOf(nonEmptyList))));

        return Formula.and(spec);
    }

    /**
     * Returns a formula stating that two lists are prefixes of one another iff they
     * are equivalent.
     *
     * @return a formula stating that two lists are prefixes of one another iff they
     *         are equivalent.
     */
    public Formula equivPrefix() {
        final Variable a = Variable.unary("a"), b = Variable.unary("b");
        return prefix(a, b).and(prefix(b, a)).iff(equiv(a, b)).forAll(a.oneOf(list).and(b.oneOf(list)));
    }

    /**
     * Returns a formula stating that a list that is equivalent to all of its
     * prefixes contains at most one thing.
     *
     * @return a formula stating that a list that is equivalent to all of its
     *         prefixes contains at most one thing.
     */
    public Formula loneList() {
        final Variable a = Variable.unary("a");
        return prefixes(a).eq(equivTo(a)).implies(cdr(a).in(emptyList)).forAll(a.oneOf(list));
    }

    /**
     * Returns a formula stating that the prefix relation is transitive over
     * non-empty lists.
     *
     * @return a formula stating that the prefix relation is transitive over
     *         non-empty lists.
     */
    public Formula transitivePrefixes() {
        final Variable a = Variable.unary("a"), b = Variable.unary("b"), c = Variable.unary("c");
        return prefix(a, b).and(prefix(b, c)).implies(prefix(a, c)).forAll(a.oneOf(nonEmptyList).and(b.oneOf(nonEmptyList)).and(c.oneOf(nonEmptyList)));
    }

    /**
     * Returns a formula stating that all lists are acyclic.
     *
     * @return a formula stating that all lists are acyclic.
     */
    public Formula acyclicity() {
        // all a: List | a !in a.^cdr
        final Variable a = Variable.unary("a");
        return a.in(cdr(a)).not().forAll(a.oneOf(list));
    }

    /**
     * Returns a formula stating that the equivTo relation is reflexive.
     *
     * @return negation of a formula stating that the equivTo relation is reflexive.
     */
    public Formula equivReflexivity() {
        // all L: List | L in L.equivTo
        final Variable a = Variable.unary("a");
        return a.in(equivTo(a)).forAll(a.oneOf(list));
    }

    /**
     * Returns the bounds for the toy lists problem with the given number of lists
     * and things.
     *
     * @return bounds for the toy lists problem with the given number of lists and
     *         things.
     */
    public Bounds bounds(int lists, int things) {
        final List<String> atoms = new ArrayList<String>(lists + things);
        for (int i = 0; i < lists; i++) {
            atoms.add("list" + i);
        }
        for (int i = 0; i < things; i++) {
            atoms.add("thing" + i);
        }
        final Universe univ = new Universe(atoms);
        final TupleFactory f = univ.factory();
        final Bounds b = new Bounds(univ);

        b.bound(list, f.range(f.tuple("list0"), f.tuple("list" + (lists - 1))));
        b.bound(nonEmptyList, b.upperBound(list));
        b.bound(emptyList, b.upperBound(list));

        b.bound(thing, f.range(f.tuple("thing0"), f.tuple("thing" + (things - 1))));

        b.bound(car, b.upperBound(nonEmptyList).product(b.upperBound(thing)));
        b.bound(cdr, b.upperBound(nonEmptyList).product(b.upperBound(list)));
        b.bound(equivTo, b.upperBound(list).product(b.upperBound(list)));
        b.bound(prefixes, b.upperBound(list).product(b.upperBound(list)));

        return b;
    }

    private static void usage() {
        System.out.println("Usage: java examples.alloy.ToyLists <# of lists> <# of things> <id of assertion to check>");
        System.exit(1);
    }

    /**
     * Usage: java examples.alloy.ToyLists <# of lists> <# of things> <id of
     * assertion to check or 0 to just run the spec>
     */
    public static void main(String[] args) {
        if (args.length < 3)
            usage();
        try {
            final int l = Integer.parseInt(args[0]);
            final int t = Integer.parseInt(args[1]);
            final int a = Integer.parseInt(args[2]);
            final ToyLists model = new ToyLists();

            final Bounds b = model.bounds(l, t);
            final Solver solver = new Solver();
            solver.options().setSolver(SATFactory.MiniSatProver);
            solver.options().setLogTranslation(1);
            solver.options().setSymmetryBreaking(1000);

            final Formula f;
            switch (a) {
                case 0 :
                    f = model.spec();
                    break;
                case 1 :
                    f = model.spec().and(model.equivPrefix().not());
                    break;
                case 2 :
                    f = model.spec().and(model.loneList().not());
                    break;
                case 3 :
                    f = model.spec().and(model.transitivePrefixes().not());
                    break;
                case 4 :
                    f = model.spec().and(model.acyclicity().not());
                    break;
                case 5 :
                    f = model.spec().and(model.equivReflexivity().not());
                    break;
                default :
                    usage();
                    throw new AssertionError("dead code");
            }

            final Solution sol = solver.solve(f, b);
            if (sol.instance() != null) {
                System.out.println(sol);
            } else {
                System.out.println(sol.outcome());
                System.out.println(sol.stats());

                System.out.println("Top level formulas: " + sol.proof().log().roots().size());
                System.out.println("Initial core: " + sol.proof().highLevelCore().size());

                sol.proof().minimize(new AdaptiveRCEStrategy(sol.proof().log()));

                System.out.println("Minimal core: " + sol.proof().highLevelCore().size());

                final Set<Formula> core = Nodes.allRoots(f, sol.proof().highLevelCore().values());

                for (Formula c : core) {
                    System.out.println(c);
                }

                System.out.print("checking the core ... ");
                if (solver.solve(Formula.and(core), b).instance() == null) {
                    System.out.println("correct.");
                } else {
                    System.out.println("incorrect!");
                }
            }

        } catch (NumberFormatException nfe) {
            usage();
        }
    }

}
