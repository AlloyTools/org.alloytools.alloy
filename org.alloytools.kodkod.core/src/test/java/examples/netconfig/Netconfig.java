package examples.netconfig;

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
 * A kodkod encoding of netconfig.als:
 *
 * <pre>
 *
 * module internal/netconfig2 open util/ordering[Time] as tick
 *
 * sig Time {}
 *
 * abstract sig Site {}
 * sig HQ, Sub extends Site {}
 *
 * sig Router {
 *  site: Site,
 *  satellite: Router -> Time,
 *  lineOfSight: Router -> Time
 * }
 *
 * pred invariants() {
 *  -- every site has at least one Router Site in Router.site
 *  -- links are symmetric and non-reflexive
 *  all t: Time | lineOfSight.t = ~(lineOfSight.t) && no lineOfSight.t & iden
 *  all t: Time | satellite.t = ~(satellite.t) && no satellite.t & iden
 *
 *  -- no two Routers are connected with two both a satellite and lineOfSight
 *  -- link at the same Time
 *  all t: Time | no satellite.t & lineOfSight.t
 *
 *  -- there is at most one satellite link at any given Time: a resource constraint
 *  all t: Time | no satellite || some r1, r2: Router | r1->r2 + r2->r1 = satellite.t
 * }
 *
 * pred subsConnectedToHQ(endTime: Time) {
 *  -- every Sub location is connected to an HQ location at the given Time
 *  all subRouter: site.Sub | some hqRouter: site.HQ |
 *   subRouter->hqRouter in (satellite + lineOfSight).endTime
 * }
 *
 * pred connectedSites(sites: set Site, endTime: Time) {
 *  -- all sites in the given set are connected to each other at the given Time
 *  all s: sites | some r: site.s |
 *   sites - s in (r.^((satellite + lineOfSight).endTime)).site
 * }
 *
 * pred addSatelliteLink(r1, r2: Router, t: Time) { r1->r2 in satellite.t }
 *
 * pred addLineOfSightLink(r1, r2: Router, t: Time) {
 *  r1->r2 in satellite.tick/prev(t) && r1->r2 in lineOfSight.t }
 *
 * pred continuedConnection(r1, r2: Router, t: Time) {
 *  r1->r2 & lineOfSight.tick/prev(t) = r1->r2 & lineOfSight.t }
 *
 * pred lostConnection(r1, r2: Router, t: Time) {
 *  r1->r2 in lineOfSight.tick/prev(t) && no r1->r2 & lineOfSight.t }
 *
 * pred traces() {
 *  all r1, r2: Router, t: Time |
 *   addSatelliteLink(r1, r2, t) || addLineOfSightLink(r1, r2, t) ||
 *   continuedConnection(r1, r2, t) || lostConnection(r1, r2, t) }
 *
 * pred show() {
 *  invariants() && subsConnectedToHQ(tick/last()) &&
 *  connectedSites(Site, tick/last()) && traces() }
 *
 * --75.03 secs with Berkmin, p cnf 36512 499783
 * run show for exactly 1 HQ, exactly 9 Sub, exactly 10 Router, exactly 9 Time
 * </pre>
 *
 * @author Emina Torlak
 */
public class Netconfig {

    // sigs
    private final Relation Time, Router, Site, HQ, Sub;
    // fields
    private final Relation site, satellite, lineOfSight, start, end, tick;

    /**
     * Constructs an instance of the Netconfig problem.
     */
    public Netconfig() {
        Time = Relation.unary("Time");
        start = Relation.unary("start");
        end = Relation.unary("end");
        tick = Relation.binary("tick");
        Router = Relation.unary("Router");
        Site = Relation.unary("Site");
        HQ = Relation.unary("HQ");
        Sub = Relation.unary("Sub");
        site = Relation.binary("site");
        satellite = Relation.ternary("satellite");
        lineOfSight = Relation.ternary("lineOfSight");
    }

    /**
     * Returns a formula stating that r is symmetric and non reflexive.
     *
     * @requires r.arity = 2
     * @return r = ~r && no r & iden
     */
    private final Formula symmNonRefl(Expression r) {
        assert r.arity() == 2;
        return r.eq(r.transpose()).and(r.intersection(Expression.IDEN).no());
    }

    /**
     * Returns the constraints implicit in signature and field declarations.
     *
     * @return the constraints implicit in signature and field declarations.
     */
    public Formula declarations() {
        // HQ + Sub in Site && no HQ & Sub
        final Formula hqSub = HQ.union(Sub).in(Site).and(HQ.intersection(Sub).no());
        // site is a function from Router to Site
        final Formula siteFun = site.function(Router, Site);
        // satellite in Router->Router->Time && lineOfSight in
        // Router->Router->Time
        final Expression rrt = Router.product(Router).product(Time);
        final Formula satLos = satellite.in(rrt).and(lineOfSight.in(rrt));
        // tick is a total ordering on time
        final Formula tord = tick.totalOrder(Time, start, end);
        return hqSub.and(siteFun).and(satLos).and(tord);

    }

    /**
     * Returns the invariants predicate.
     *
     * @return invariants
     */
    public Formula invariants() {
        final Variable t = Variable.unary("t");

        final Expression losAtT = lineOfSight.join(t);
        final Expression satAtT = satellite.join(t);
        final Formula symNonRefl = symmNonRefl(losAtT).and(symmNonRefl(satAtT));
        final Formula noSatAndLos = satAtT.intersection(losAtT).no();

        final Variable r1 = Variable.unary("r1");
        final Variable r2 = Variable.unary("r2");
        final Expression productUnion = r1.product(r2).union(r2.product(r1));
        final Formula someSatAtT = productUnion.eq(satAtT).forSome(r1.oneOf(Router).and(r2.oneOf(Router)));
        final Formula loneSatAtT = satellite.no().or(someSatAtT);

        return symNonRefl.and(noSatAndLos).and(loneSatAtT).forAll(t.oneOf(Time));
    }

    /**
     * Returns the subsConnectedToHQ predicate.
     *
     * @return subsConnectedToHQ }
     */
    public Formula subsConnectedToHQ(Expression endTime) {
        final Variable subRouter = Variable.unary("subRouter");
        final Variable hqRouter = Variable.unary("hqRouter");
        final Formula f = subRouter.product(hqRouter).in(satellite.union(lineOfSight).join(endTime));
        return f.forSome(hqRouter.oneOf(site.join(HQ))).forAll(subRouter.oneOf(site.join(Sub)));
    }

    /**
     * Returns the connectedSites predicate.
     *
     * @return connectedSites
     */
    public Formula connectedSites(Expression sites, Expression endTime) {
        final Variable s = Variable.unary("s");
        final Variable r = Variable.unary("r");
        final Expression linksAtEndTime = satellite.union(lineOfSight).join(endTime);
        final Formula f = sites.difference(s).in(r.join(linksAtEndTime.closure()).join(site));
        return f.forSome(r.oneOf(site.join(s))).forAll(s.oneOf(sites));
    }

    /**
     * Returns the addSatelliteLink predicate
     *
     * @return addSatelliteLink
     */
    public Formula addSatelliteLink(Expression r1, Expression r2, Expression t) {
        return r1.product(r2).in(satellite.join(t));
    }

    /**
     * Returns the addLineOfSightLink predicate.
     *
     * @return addLineOfSightLink
     */
    public Formula addLineOfSightLink(Expression r1, Expression r2, Expression t) {
        final Expression link = r1.product(r2);
        return link.in(satellite.join(tick.join(t))).and(link.in(lineOfSight.join(t)));
    }

    /**
     * Returns the continuedConnection predicate.
     *
     * @return continuedConnection
     */
    public Formula continuedConnection(Expression r1, Expression r2, Expression t) {
        final Expression link = r1.product(r2);
        return link.intersection(lineOfSight.join(tick.join(t))).eq(link.intersection(lineOfSight.join(t)));
    }

    /**
     * Returns the lostConnection predicate.
     *
     * @return lostConnection
     */
    public Formula lostConnection(Expression r1, Expression r2, Expression t) {
        final Expression link = r1.product(r2);
        return link.in(lineOfSight.join(tick.join(t))).and(link.intersection(lineOfSight.join(t)).no());
    }

    /**
     * Returns the traces predicate.
     *
     * @return traces
     */
    public Formula traces() {
        final Variable r1 = Variable.unary("r1");
        final Variable r2 = Variable.unary("r2");
        final Variable t = Variable.unary("t");

        final Formula f = addSatelliteLink(r1, r2, t).or(addLineOfSightLink(r1, r2, t)).or(continuedConnection(r1, r2, t)).or(lostConnection(r1, r2, t));

        return f.forAll(r1.oneOf(Router).and(r2.oneOf(Router)).and(t.oneOf(Time)));

    }

    /**
     * Returns the show predicate.
     *
     * @return show
     */
    public Formula show() {
        return declarations().and(invariants()).and(subsConnectedToHQ(end)).and(connectedSites(Site, end)).and(traces());
    }

    /**
     * Returns a bounds object that constructs the 'scope' for analyzing the
     * commands, using the given values for the number of sites, routers, and the
     * length of time.
     *
     * @requires all arguments are positive and hqNum <= siteNum
     * @return a bounds for the model
     */
    public Bounds bounds(int siteNum, int hqNum, int routerNum, int timeLength) {
        assert siteNum > 0 && hqNum > 0 && hqNum <= siteNum && routerNum > 0 && timeLength > 0;
        final List<String> atoms = new ArrayList<String>(siteNum + routerNum + timeLength);
        for (int i = 0; i < siteNum; i++) {
            atoms.add("Site" + i);
        }
        for (int i = 0; i < routerNum; i++) {
            atoms.add("Router" + i);
        }
        for (int i = 0; i < timeLength; i++) {
            atoms.add("Time" + i);
        }
        final Universe u = new Universe(atoms);
        final TupleFactory f = u.factory();

        final Bounds b = new Bounds(u);

        final String site0 = "Site0";
        final String siteN = "Site" + (siteNum - 1);

        final TupleSet sBound = f.range(f.tuple(site0), f.tuple(siteN));
        b.boundExactly(Site, sBound);
        b.boundExactly(HQ, f.range(f.tuple(site0), f.tuple("Site" + (hqNum - 1))));
        if (hqNum < siteNum) {
            b.boundExactly(Sub, f.range(f.tuple("Site" + hqNum), f.tuple(siteN)));
        } else {
            b.bound(Sub, f.noneOf(1));
        }

        final TupleSet tBound = f.range(f.tuple("Time0"), f.tuple("Time" + (timeLength - 1)));
        b.bound(Time, tBound);
        b.bound(start, tBound);
        b.bound(end, tBound);
        b.bound(tick, tBound.product(tBound));

        final TupleSet rBound = f.range(f.tuple("Router0"), f.tuple("Router" + (routerNum - 1)));
        b.boundExactly(Router, rBound);
        // b.bound(site, rBound.product(sBound));
        b.bound(satellite, rBound.product(rBound).product(tBound));
        b.bound(lineOfSight, b.upperBound(satellite));

        assert siteNum == routerNum;
        final TupleSet siteBound = f.noneOf(2);
        for (int i = 0; i < siteNum; i++)
            siteBound.add(f.tuple("Router" + i, "Site" + i));
        b.boundExactly(site, siteBound);// rBound.product(sBound));

        return b;
    }

    private static final void usage() {
        System.out.println("Usage: java examples.Netconfig [# sites] [# hq] [# routers] [# time steps]");
        System.exit(1);
    }

    /**
     * Usage: java examples.Netconfig [# sites] [# hq] [# routers] [# time steps]
     */
    public static void main(String[] args) {
        if (args.length < 4)
            usage();
        final Netconfig model = new Netconfig();
        final Solver solver = new Solver();
        // solver.options().setSolver(SATFactory.ZChaffMincost);
        solver.options().setSolver(SATFactory.MiniSat);
        try {
            final Formula show = model.show();
            final Solution sol = solver.solve(show, model.bounds(Integer.parseInt(args[0]), Integer.parseInt(args[1]), Integer.parseInt(args[2]), Integer.parseInt(args[3])));
            // System.out.println(show);
            // System.out.println("p cnf " +
            // (solver.numberOfIntermediateVariables()+solver.numberOfPrimaryVariables())
            // + " " + solver.numberOfClauses());
            System.out.println(sol.outcome());
            System.out.println(sol.stats());

        } catch (NumberFormatException nfe) {
            usage();
        }
    }
}
