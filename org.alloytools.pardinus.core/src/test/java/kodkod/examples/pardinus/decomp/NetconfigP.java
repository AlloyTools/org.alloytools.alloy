package kodkod.examples.pardinus.decomp;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.decomp.DModel;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

public class NetconfigP extends DModel {

	// sigs
	private final Relation Time, Router, Site, HQ, Sub;
	// fields
	private final Relation site, satellite, lineOfSight, start, end, tick;
	
	private final Universe u;
	
	private int timeLength, siteNum, hqNum, routerNum;
	
	/**
	 * Creates an instance of Dijkstra example.
	 */
	public NetconfigP(String[] args) {
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
		
		siteNum = Integer.valueOf(args[0]);
		hqNum = Integer.valueOf(args[1]);
		routerNum = Integer.valueOf(args[2]);
		timeLength = Integer.valueOf(args[3]);

		assert siteNum > 0 && hqNum > 0 && hqNum <= siteNum && routerNum > 0 && timeLength > 0;
		final List<String> atoms = new ArrayList<String>(siteNum+routerNum+timeLength);
		for(int i = 0; i < siteNum; i++) {
			atoms.add("Site"+i);
		}
		for(int i = 0; i < routerNum; i++) {
			atoms.add("Router"+i);
		}
		for(int i = 0; i < timeLength; i++) {
			atoms.add("Time"+i);
		}

		u = new Universe(atoms);
	}


	/**
	 * Returns a formula stating that r is symmetric and non reflexive.
	 * @requires r.arity = 2
	 * @return r = ~r && no r & iden
	 */
	private final Formula symmNonRefl(Expression r) {
		assert r.arity() == 2;
		return r.eq(r.transpose()).and(r.intersection(Expression.IDEN).no());
	}
	
	/**
	 * Returns the constraints implicit in signature and field declarations.
	 * @return the constraints implicit in signature and field declarations.
	 */
	public Formula declarations() {
		// satellite in Router->Router->Time && lineOfSight in Router->Router->Time
		final Expression rrt = Router.product(Router).product(Time);
		final Formula satLos = satellite.in(rrt).and(lineOfSight.in(rrt));
		// tick is a total ordering on time
		final Formula tord = tick.totalOrder(Time, start, end);
		return satLos.and(tord);
		
	}
	
	/**
	 * Returns the invariants predicate.
	 * @return  invariants 
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
	 * @return  subsConnectedToHQ 
	 * }
	 */
	public Formula subsConnectedToHQ(Expression endTime) {
		final Variable subRouter = Variable.unary("subRouter");
		final Variable hqRouter = Variable.unary("hqRouter");
		final Formula f = subRouter.product(hqRouter).in(satellite.union(lineOfSight).join(endTime));
		return f.forSome(hqRouter.oneOf(site.join(HQ))).forAll(subRouter.oneOf(site.join(Sub)));
	}
	
	/**
	 * Returns the connectedSites predicate.
	 * @return  connectedSites 
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
	 * @return addSatelliteLink
	 */
	public Formula addSatelliteLink(Expression r1, Expression r2, Expression t) {
		return r1.product(r2).in(satellite.join(t));
	}
	
	/**
	 * Returns the addLineOfSightLink predicate.
	 * @return addLineOfSightLink
	 */
	public Formula addLineOfSightLink(Expression r1, Expression r2, Expression t) {
		final Expression link = r1.product(r2);
		return link.in(satellite.join(tick.join(t))).and(link.in(lineOfSight.join(t)));
	}
	
	/**
	 * Returns the continuedConnection predicate.
	 * @return continuedConnection
	 */
	public Formula continuedConnection(Expression r1, Expression r2, Expression t) {
		final Expression link = r1.product(r2);
		return link.intersection(lineOfSight.join(tick.join(t))).eq(link.intersection(lineOfSight.join(t)));
	}
 
	/** 
	 * Returns the lostConnection predicate.
	 * @return lostConnection
	 */
	public Formula lostConnection(Expression r1, Expression r2, Expression t) {
		final Expression link = r1.product(r2);
		return link.in(lineOfSight.join(tick.join(t))).and(link.intersection(lineOfSight.join(t)).no());
	}
	
	/**
	 * Returns the traces predicate.
	 * @return traces
	 */
	public Formula traces() {
		final Variable r1 = Variable.unary("r1");
		final Variable r2 = Variable.unary("r2");
		final Variable t = Variable.unary("t");
		
		final Formula f = addSatelliteLink(r1, r2, t).or(addLineOfSightLink(r1, r2, t)).
		                  or(continuedConnection(r1, r2, t)).or(lostConnection(r1, r2, t));
		
		return f.forAll(r1.oneOf(Router).and(r2.oneOf(Router)).and(t.oneOf(Time)));
		
	}
	
	/**
	 * Returns the show predicate.
	 * @return show
	 */
	public Formula show() {
		return declarations().and(invariants()).and(subsConnectedToHQ(end)).
		       and(connectedSites(Site, end)).and(traces());
	}
	

	@Override
	public PardinusBounds bounds1() {
		final TupleFactory f = u.factory();
		final PardinusBounds b = new PardinusBounds(u);
				

		final TupleSet sBound = f.range(f.tuple("Site0"), f.tuple("Site" + (siteNum-1)));
		final TupleSet sBound1 = f.range(f.tuple("Site0"), f.tuple("Site" + (hqNum-1)));
		final TupleSet sBound2 = f.range(f.tuple("Site"+hqNum), f.tuple("Site" + (siteNum-1)));
		
		b.boundExactly(Site, sBound);
		b.boundExactly(HQ, sBound1);
		if (hqNum < siteNum) {
			b.boundExactly(Sub, sBound2);
		} else {
			b.bound(Sub, f.noneOf(1));
		}
				
		final TupleSet rBound = f.range(f.tuple("Router0"), f.tuple("Router"+(routerNum-1)));
		b.boundExactly(Router, rBound);	
		//b.bound(site, rBound.product(sBound));
		
		assert siteNum == routerNum;
		final TupleSet siteBound = f.noneOf(2);
		for(int i = 0; i < siteNum; i++)
			siteBound.add(f.tuple("Router"+i, "Site"+i));
		b.boundExactly(site, siteBound);//rBound.product(sBound));
			
			
		return b;	
	}

	@Override
	public Bounds bounds2() {
		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);
		
		final TupleSet tBound = f.range(f.tuple("Time0"), f.tuple("Time" + (timeLength-1)));
		
		b.bound(Time, tBound);
		b.bound(start, tBound);
		b.bound(end, tBound);
		b.bound(tick, tBound.product(tBound));
		
		final TupleSet rBound = f.range(f.tuple("Router0"), f.tuple("Router"+(routerNum-1)));

		b.bound(satellite, rBound.product(rBound).product(tBound));
		b.bound(lineOfSight, rBound.product(rBound).product(tBound));
			
		return b;
	}

	@Override
	public Formula partition1() {
		// HQ + Sub in Site && no HQ & Sub
		final Formula hqSub = HQ.union(Sub).in(Site).and(HQ.intersection(Sub).no());
		// site is a function from Router to Site
		final Formula siteFun = site.function(Router, Site);
		
		return hqSub.and(siteFun);

	}

	@Override
	public Formula partition2() {
		return show();
	}

	@Override
	public int getBitwidth() {
		return 1;
	}


	@Override
	public String shortName() {
		// TODO Auto-generated method stub
		return null;
	}
}
