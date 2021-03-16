package examples.alloy;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

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
 * Kodkod encoding of the DNA cuts model:
 *
 * <pre>
 * module s2
 *
 * open util/ordering[Link]
 *
 * abstract sig Base { partner: one Base }
 * one sig A, T, G, C extends Base {}
 *
 * fact partners {
 *  A.partner = T
 *  T.partner = A
 *  G.partner = C
 *  C.partner = G }
 *
 * abstract sig Link { base: one Base }
 *
 * sig CutLink, JoinLink extends Link {}
 *
 * fact CutChainsAtMost6BasesLong {
 *  all c: CutLink |
 *   next(c) in JoinLink || next(next(c)) in JoinLink ||
 *   next(next(next(c))) in JoinLink ||
 *   next(next(next(next(c)))) in JoinLink ||
 *   next(next(next(next(next(c))))) in JoinLink }
 *
 * pred noMatch(l1, l2: Link) {
 *   l1 in JoinLink || l2 in JoinLink ||
 *   l1.base !in (l1.base + l2.base.partner) }
 *
 * fact CutLinkUniqueness {
 *  all c1, c2 : CutLink |
 *   c1 != c2 && prev(c1) in JoinLink && prev(c2) in JoinLink => {
 *    c1.base != (c2.base + c2.base.partner) ||
 *    noMatch(next(c1), next(c2)) || noMatch(next(next(c1)), next(next(c2))) ||
 *    noMatch(next(next(next(c1))), next(next(next(c2)))) ||
 *    noMatch(next(next(next(next(c1)))), next(next(next(next(c2))))) ||
 *    noMatch(next(next(next(next(next(c1))))), next(next(next(next(next(c2)))))) } }
 *
 *
 * pred show () {
 *  Base in Link.base
 *  some JoinLink
 *  some disj c1, c2, c3, c4, c5: CutLink |
 *   prev(c1) in JoinLink &&
 *   next(c1) = c2 && next(c2) = c3 &&
 *   next(c3) in JoinLink && next(c4) = c5 &&
 *   next(c5) in JoinLink }
 *
 * run show for exactly 11 Link
 * </pre>
 *
 * @author Emina Torlak
 */
public final class DNACuts {

    private final Relation     next, Link, CutLink, JoinLink, Base, base, partner;
    private final Expression[] neighbor;

    /**
     * Constructs an instance of the DNACuts example for the given cut link length.
     */
    public DNACuts(int cutLinkLength) {
        assert cutLinkLength > 0;
        Base = Relation.unary("Base");
        Link = Relation.unary("Link");
        CutLink = Relation.unary("CutLink");
        JoinLink = Relation.unary("JoinLink");
        base = Relation.binary("base");
        next = Relation.binary("next");
        partner = Relation.binary("partner");
        neighbor = new Expression[cutLinkLength - 1];
        if (cutLinkLength > 1) {
            neighbor[0] = next;
            for (int i = 1; i < cutLinkLength - 1; i++) {
                neighbor[i] = next.join(neighbor[i - 1]);
            }
        }

    }

    /**
     * Returns declarations constraints.
     *
     * @return declarations constraints.
     */
    public Formula declarations() {
        final Variable l = Variable.unary("l");
        final Formula f0 = l.join(base).one().forAll(l.oneOf(Link));
        final Formula f1 = CutLink.union(JoinLink).eq(Link);
        final Formula f2 = CutLink.intersection(JoinLink).no();
        return f0.and(f1).and(f2);
    }

    /**
     * Returns the cutChainLength constraint. (Similar to CutChainsAtMost6BasesLong
     * fact, but with the cut chain length as specified during construction.)
     *
     * @return the cutChainLength constraint
     */
    public Formula cutChainLength() {
        Formula ret = Formula.FALSE;
        final Variable c = Variable.unary("c");
        for (int i = 0; i < neighbor.length; i++) {
            ret = ret.or(c.join(neighbor[i]).in(JoinLink));
        }
        return ret.forAll(c.oneOf(CutLink));
    }

    /**
     * Returns the cutLinkUniqueness constraint.
     *
     * @return the cutLinkUniqueness constraint.
     */
    public Formula cutLinkUniqueness() {
        final Variable c1 = Variable.unary("c1");
        final Variable c2 = Variable.unary("c2");
        final Formula f0 = c1.eq(c2).not().and(next.join(c1).in(JoinLink)).and(next.join(c2).in(JoinLink));
        Formula f = c1.join(base).in(c2.join(base).union(c2.join(base).join(partner))).not();
        for (int i = 0; i < neighbor.length; i++) {
            Expression c1n = c1.join(neighbor[i]), c2n = c2.join(neighbor[i]);
            f = f.or(c1n.in(JoinLink)).or(c2n.in(JoinLink));
            f = f.or(c1n.join(base).in(c2n.join(base).union(c2n.join(base).join(partner))).not());
        }
        return f0.implies(f).forAll(c1.oneOf(CutLink).and(c2.oneOf(CutLink)));
    }

    /**
     * Returns the show predicate.
     *
     * @return the show predicate.
     */
    public Formula show() {
        final Formula f0 = Base.in(Link.join(base));
        final Formula f1 = JoinLink.some();
        final Formula f2 = CutLink.some();
        return declarations().and(cutChainLength()).and(cutLinkUniqueness()).and(f0).and(f1).and(f2);
    }

    /**
     * Returns the bounds for n links.
     *
     * @return bounds for n links.
     */
    public Bounds bounds(int n) {
        assert n >= 0;
        final List<String> atoms = new ArrayList<String>(n + 4);
        atoms.add("A");
        atoms.add("T");
        atoms.add("G");
        atoms.add("C");
        for (int i = 0; i < n; i++) {
            atoms.add("Link" + i);
        }
        final Universe u = new Universe(atoms);
        final TupleFactory f = u.factory();
        final Bounds b = new Bounds(u);

        final TupleSet bases = f.range(f.tuple("A"), f.tuple("C"));
        final TupleSet links = f.range(f.tuple("Link0"), f.tuple("Link" + (n - 1)));

        b.boundExactly(Base, bases);
        b.boundExactly(Link, links);
        b.bound(CutLink, links);
        b.bound(JoinLink, links);

        final TupleSet randomSequence = f.noneOf(2);
        final Random r = new Random();
        for (int i = 0; i < n; i++) {
            randomSequence.add(f.tuple("Link" + i, u.atom(r.nextInt(4))));
        }
        b.boundExactly(base, randomSequence);

        final TupleSet partners = f.noneOf(2);
        partners.add(f.tuple("A", "T"));
        partners.add(f.tuple("T", "A"));
        partners.add(f.tuple("G", "C"));
        partners.add(f.tuple("C", "G"));

        b.boundExactly(partner, partners);

        final TupleSet linkOrd = f.noneOf(2);
        for (int i = 1; i < n; i++) {
            linkOrd.add(f.tuple("Link" + (i - 1), "Link" + i));
        }

        b.boundExactly(next, linkOrd);

        return b;
    }

    private static void usage() {
        System.out.println("Usage: java examples.alloy.DNACuts [cut chain length] [# links]");
        System.exit(1);
    }

    /**
     * Usage: java examples.alloy.DNACuts [cut chain length] [# links]
     */
    public static void main(String[] args) {
        if (args.length < 2)
            usage();

        try {
            final DNACuts model = new DNACuts(Integer.parseInt(args[0]));
            final Solver solver = new Solver();
            solver.options().setSolver(SATFactory.DefaultSAT4J);
            Formula f = model.show();
            Bounds b = model.bounds(Integer.parseInt(args[1]));
            System.out.println("solving...");
            Solution sol = solver.solve(f, b);
            // System.out.println(f);
            // System.out.println(b);
            System.out.println(sol.outcome());
            System.out.println(sol.stats());
        } catch (NumberFormatException nfe) {
            usage();
        }
    }
}
