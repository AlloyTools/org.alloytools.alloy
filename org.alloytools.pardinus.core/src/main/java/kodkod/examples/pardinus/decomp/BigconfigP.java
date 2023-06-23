package kodkod.examples.pardinus.decomp;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solver;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.DecomposedOptions.DMode;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 * A kodkod encoding of bigconfig.als:
 * 
 * <pre>
 *  module internal/bigconfig
 *  
 *  abstract sig Site {}
 *  sig HQ, Sub extends Site {}
 * 
 *  sig Router {
 *  site: Site,
 *  link: set Router
 *  }
 * 
 *  pred invariants() {
 *  -- every site has at least one router  
 *  Site in Router.site
 *  
 *  -- links are symmetric and non-reflexive
 *  link = ~link 
 *  no link &amp; iden
 *  }
 * 
 *  pred subsConnectedToHQ() {
 *  -- every sub location is connected to an HQ location at the given time
 *  site.Sub in (site.HQ).link
 *  }
 * 
 *  pred connectedSites(sites: set Site) {
 *  -- all sites in the given set are connected to each other  
 *  all s: sites | sites - s in ((site.s).&circ;link).site
 *  }
 * 
 *  pred show() {
 *  invariants() &amp;&amp; subsConnectedToHQ() &amp;&amp; connectedSites(Site) 
 *  }
 * </pre>
 * 
 * @author Emina Torlak
 */
public class BigconfigP {

	private static Universe universe;

	// sigs
	private final Relation Router, Site, HQ, Sub;
	// fields
	private final Relation site, link;

	private final int closureApprox;

	/**
	 * Constructs an instance of the BigConfig example.
	 */
	public BigconfigP(int closureApprox) {
		Router = Relation.unary("Router");
		Site = Relation.unary("Site");
		HQ = Relation.unary("HQ");
		Sub = Relation.unary("Sub");
		site = Relation.binary("site");
		link = Relation.binary("link");
		this.closureApprox = closureApprox;
	}

	/**
	 * Returns the constraints implicit in signature and field declarations.
	 * 
	 * @return abstract sig Site {} sig HQ, Sub extends Site {}
	 * 
	 *         sig Router { site: Site, link: set Router }
	 */
	public Formula declarations1() {
		// HQ + Sub in Site && no HQ & Sub
		final Formula hqSub = HQ.union(Sub).in(Site).and(HQ.intersection(Sub).no());

		
		// link in Router->Router
		final Formula links = link.in(Router.product(Router));

		return hqSub.and(links);
	}

	public Formula declarations2() {
		// site is a function from Router to Site
		final Formula siteFun = site.function(Router, Site);
		return siteFun;
	}

	/**
	 * Returns the invariants predicate.
	 * 
	 * @return pred invariants() { -- every site has at least one router Site in
	 *         Router.site
	 * 
	 *         -- links are symmetric and non-reflexive link = ~link no link &
	 *         iden }
	 */
	public Formula invariants2() {
		Formula atLeastARouter = Site.in(Router.join(site));
		return atLeastARouter;
	}

	public Formula invariants1() {
		Formula linksSymmetric = link.eq(link.transpose());
		Formula linksNotReflexive = link.intersection(Expression.IDEN).no();
		return (linksSymmetric).and(linksNotReflexive);
	}

	/**
	 * Returns the subsConnectedToHQ predicate.
	 * 
	 * @return pred subsConnectedToHQ() { -- every sub location is connected to
	 *         an HQ location at the given time site.Sub in (site.HQ).link }
	 */
	public Formula subsConnectedToHQ() {
		return site.join(Sub).in(site.join(HQ).join(link));
	}

	/**
	 * Returns the connectedSites predicate.
	 * 
	 * @return pred connectedSites(sites: set Site) { -- all sites in the given
	 *         set are connected to each other all s: sites | sites - s in
	 *         ((site.s).^link).site }
	 */
	public Formula connectedSites(Expression sites) {
		final Variable s = Variable.unary("s");
		Expression closed;
		if (closureApprox > 0) {
			closed = link;
			for (int i = 1; i < closureApprox; i *= 2) {
				closed = closed.union(closed.join(closed));
			}
		} else {
			closed = link.closure();
		}

		final Expression sreachable = site.join(s).join(closed).join(site);
		final Formula f = sites.difference(s).in(sreachable);
		return f.forAll(s.oneOf(sites));
	}

	/**
	 * Returns the show predicate.
	 * 
	 * @return pred show() { invariants() && subsConnectedToHQ() &&
	 *         connectedSites(Site) }
	 */
	public Formula show() {
		return declarations2().and(invariants2()).and(subsConnectedToHQ()).and(connectedSites(Site));
	}

	/**
	 * @return a universe with n routers and n sites. The first n atoms are
	 *         sites.
	 */
	private static Universe universe(int n) {
		final List<String> atoms = new ArrayList<String>(n * 2);
		for (int i = 0; i < n; i++) {
			atoms.add("Site" + i);
		}
		for (int i = 0; i < n; i++) {
			atoms.add("Router" + i);
		}
		return new Universe(atoms);
	}

	/**
	 * Returns a bounds with the given number of hqs and subs, constructed using
	 * the given universe.
	 * 
	 * @requires hqNum > 0 && subNum > 0
	 * @requires u contains at least (hqNum+sub) Router atoms and as many Site
	 *           atoms
	 * @return bounds
	 */
	private Bounds bounds1(int hqNum, int subNum, Universe u) {
		final TupleFactory f = u.factory();

		final Bounds b = new Bounds(u);
		final int siteMax = hqNum + subNum - 1;

		final String site0 = "Site0";
		final String siteN = "Site" + siteMax;
		final String siteHQ = "Site" + (hqNum - 1);
		final String siteSub = "Site" + hqNum;
		final String router0 = "Router0";
		final String routerN = "Router" + siteMax;

		final TupleSet sites = f.range(f.tuple(site0), f.tuple(siteN));
		b.boundExactly(Site, sites);
		b.boundExactly(HQ, f.range(f.tuple(site0), f.tuple(siteHQ)));
		b.boundExactly(Sub, f.range(f.tuple(siteSub), f.tuple(siteN)));

		final TupleSet routers = f.range(f.tuple(router0), f.tuple(routerN));
		b.boundExactly(Router, routers);
//		final TupleSet routerLocations = f.noneOf(2);
//		for (int i = 0; i <= siteMax; i++) {
//			routerLocations.add(f.tuple("Router" + i, "Site" + i));
//		}
//		b.boundExactly(site, routerLocations);
			b.bound(link, routers.product(routers));
		return b;
	}

	private Bounds bounds2(int hqNum, int subNum, Universe u) {
		final TupleFactory f = u.factory();
		final int siteMax = hqNum + subNum - 1;

		final String site0 = "Site0";
		final String siteN = "Site" + siteMax;
		final Bounds b = new Bounds(u);
		final TupleSet sites = f.range(f.tuple(site0), f.tuple(siteN));

		final String router0 = "Router0";
		final String routerN = "Router" + siteMax;

		final TupleSet routers = f.range(f.tuple(router0), f.tuple(routerN));
		 b.bound(site, routers.product(sites));
		return b;
	}

	/**
	 * Returns a bounds with the given number of hqs and subs. The parameter
	 * routerNum designates the total number of routers in the universe.
	 * 
	 * @requires hqNum > 0 && subNum > 0
	 * @requires hqNum + subNum <= routers
	 * @return bounds
	 */
	public Bounds bounds2(int hqNum, int subNum, int routerNum) {
		assert hqNum > 0 && subNum > 0 && hqNum + subNum <= routerNum;

		return bounds2(hqNum, subNum, universe);
	}

	public Bounds bounds1(int hqNum, int subNum, int routerNum) {
		assert hqNum > 0 && subNum > 0 && hqNum + subNum <= routerNum;

		return bounds1(hqNum, subNum, universe);
	}

	private static void usage() {
		System.out
				.println("Usage: java tests.Bigconfig [# hq] [# sub] [# closure unwindings, 0 for true closure] [size of partial instance, 0 default]");
		System.exit(1);
	}

	/**
	 * Usage: java tests.Bigconfig [# hq] [# sub] [# closure unwindings, 0 for
	 * true closure] [size of partial instance, 0 default]
	 * 
	 * @throws InterruptedException
	 */
	public static void main(String[] args) throws InterruptedException {
		if (args.length < 3)
			usage();

		final BigconfigP model = new BigconfigP(Integer.parseInt(args[2]));
		final Solver solver = new Solver();
		solver.options().setSolver(SATFactory.Glucose);
		try {
			final int hq = Integer.parseInt(args[0]);
			final int sub = Integer.parseInt(args[1]);
			Integer.parseInt(args[3]);
			model.declarations1().and(model.invariants1());
			model.show();
			universe = universe(hq + sub);

			model.bounds1(hq, sub, hq + sub);
			model.bounds2(hq, sub, hq + sub);

			ExtendedOptions opt, opt2;
			
			opt = new ExtendedOptions();
			opt.setSymmetryBreaking(20);
			opt.setSolver(SATFactory.Glucose);
			opt.setDecomposedMode(DMode.PARALLEL);
			opt.setThreads(4);
			opt2 = new ExtendedOptions(opt);
			opt2.setRunTarget(false);
			opt.setConfigOptions(opt2);
			new PardinusSolver(opt);
			long start = System.currentTimeMillis();
			
//			psolver.solve(f1, f2, b1, b2);
//			
//			for (Relation r : b2.relations()) {
//				b1.bound(r, b2.lowerBound(r), b2.upperBound(r));
//			}
//			final Solution sol = solver.solve(f1.and(f2), b1);

			long end = System.currentTimeMillis();
			System.out.println(end-start);
			
//			System.out.println(sol.outcome());
//			System.out.println(sol.stats());

		} catch (NumberFormatException nfe) {
			usage();
		}
	}
}
