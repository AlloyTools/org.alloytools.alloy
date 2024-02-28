package kodkod.examples.pardinus.decomp;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.ast.operator.FormulaOperator;
import kodkod.engine.decomp.DModel;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

public final class HotelR extends DModel {

	final private int n, t;
	final private Variant variant;

	private final Relation time_init, time_end, time_loop, time_next, time_next_, time;
	private final Relation key, key_first, key_last, key_next;
	private final Relation room, guest, lastkey, current, occupant, gkeys, rkeys;
	private final Universe u;

	public enum Variant {
		INTERVENES,
		NOINTERVENES;
	}
	
	
	public HotelR(String[] args) {
		this.n = Integer.valueOf(args[0]);
		this.t = Integer.valueOf(args[1]);
		this.variant = Variant.valueOf(args[2]);
		
		time_init = Relation.unary("Time/init");
		time_end = Relation.unary("Time/end");
		time_loop = Relation.nary("Time/loop", 2);
		time_next = Relation.nary("Time/next", 2);
		time_next_ = Relation.nary("Time/next_", 2);
		time = Relation.unary("Time");
		key = Relation.unary("Key");
		guest = Relation.unary("Guest");
		room = Relation.unary("Room");
		lastkey = Relation.nary("FrontDesk.lastKey", 3);
		occupant = Relation.nary("FrontDesk.occupant", 3);
		gkeys = Relation.nary("Guest.gkeys", 3);
		rkeys = Relation.nary("Room.keys", 2);
		current = Relation.nary("Room.currentKey", 3);
		key_first = Relation.unary("ordering/Ord.First");
		key_last = Relation.unary("ordering/Ord.Last");
		key_next = Relation.nary("ordering/Ord.Next", 2);

		final List<String> atoms = new ArrayList<String>(3*n + t);
		for(int i = 0; i < n; i++) {
			atoms.add("Key"+i);
		}
		for(int i = 0; i < n; i++) {
			atoms.add("Room"+i);
		}
		for(int i = 0; i < n; i++) {
			atoms.add("Guest"+i);
		}
		for(int i = 0; i < t; i++) 
			atoms.add("Time"+i);
		
		u = new Universe(atoms);
	}

	@Override
	public PardinusBounds bounds1() {
		final TupleFactory f = u.factory();
		final PardinusBounds b = new PardinusBounds(u);
		
		final TupleSet kb = f.range(f.tuple("Key0"), f.tuple("Key"+ (n-1)));
		final TupleSet gb = f.range(f.tuple("Guest0"), f.tuple("Guest"+ (n-1)));
		final TupleSet rb = f.range(f.tuple("Room0"), f.tuple("Room"+ (n-1)));
		
		b.boundExactly(key, kb);
		b.bound(key_first, kb);
		b.bound(key_last, kb);
		b.bound(key_next, kb.product(kb));
		b.bound(guest, gb);
		b.bound(room, rb);
		b.bound(rkeys, rb.product(kb));
				
		return b;	
	}

//	@Override
//	public Bounds bounds2() {
//		final TupleFactory f = u.factory();
//		final Bounds b = new Bounds(u);
//		
//		final TupleSet kb = f.range(f.tuple("Key0"), f.tuple("Key"+ (n-1)));
//		final TupleSet gb = f.range(f.tuple("Guest0"), f.tuple("Guest"+ (n-1)));
//		final TupleSet rb = f.range(f.tuple("Room0"), f.tuple("Room"+ (n-1)));
//		final TupleSet tb = f.range(f.tuple("Time0"), f.tuple("Time"+ (t-1)));
//		
//		b.boundExactly(time, tb);
//		b.bound(time_init, tb);
//		b.bound(time_end, tb);
//		b.bound(time_loop, tb.product(tb));
//		b.bound(time_next, tb.product(tb));
//		b.bound(time_next_, tb.product(tb));
//		b.bound(lastkey, rb.product(kb).product(tb));
//		b.bound(occupant, rb.product(gb).product(tb));
//		b.bound(current, rb.product(kb).product(tb));
//		b.bound(gkeys, gb.product(kb).product(tb));
//				
//		return b;	
//	}
	
	@Override
	public Bounds bounds2() {
		final TupleFactory f = u.factory();
		final PardinusBounds b = new PardinusBounds(u);
		
		final TupleSet tb = f.range(f.tuple("Time0"), f.tuple("Time"+ (t-1)));
		
		b.boundExactly(time, tb);
		b.bound(time_init, time);
		b.bound(time_end, time);
		b.bound(time_loop, time.product(time));
		b.bound(time_next, time.product(time));
		b.bound(time_next_, time.product(time));
		b.bound(lastkey, room.product(key).product(time));
		b.bound(occupant, room.product(guest).product(time));
		b.bound(current, room.product(key).product(time));
		b.bound(gkeys, guest.product(key).product(time));
				
		return b;	
	}

	@Override
	public Formula partition1() {
		Formula x13 = rkeys.in(room.product(key)); // rkeys in Room -> Key

		Formula x28 = key_next.totalOrder(key,key_first,key_last); 

		Variable v2=Variable.unary("v5");
		Formula x41=((rkeys.join(v2)).one()).forAll(v2.oneOf(key)); // all k : Key | one rkeys.k

		Variable v3=Variable.unary("v5");
		Formula x42=((v3.join(rkeys)).some()).forAll(v3.oneOf(room)); // all r : Room | some r.rkeys

		Formula x99 = guest.eq(guest);
		
		Formula x12=Formula.compose(FormulaOperator.AND, x13, x28, x41,x99, x42);
		return x12;
	}

	@Override
	public Formula partition2() {
		Formula f2 = Formula.compose(FormulaOperator.AND, decls2(), init(), next(), noBadEntries().not());
		if (variant == Variant.NOINTERVENES) f2 = f2.and(noIntervenes());
		return f2;
	}

	private Formula decls2() {
		Formula x22 = lastkey.in(room.product(key).product(time)); // lastkey in Room -> Key -> Time
		Formula x27 = occupant.in(room.product(guest).product(time)); // occupant in Room -> Guest -> Time
		Formula x60 = gkeys.in(guest.product(key).product(time)); // gkeys in Guest -> Key -> Time
		Formula x86 = current.in(room.product(key).product(time)); // current in Room -> Key -> Time

		Variable t=Variable.unary("t");
		Variable r=Variable.unary("r");
		Formula rt1 = (r.join(lastkey.join(t))).lone(); // all t : Time, r : Room | lone r.lastkey.t 
		Formula rt2 = (r.join(current.join(t))).one(); // all t : Time, r : Room | one r.current.t 
		Formula rt3 = (r.join(current.join(t))).in(r.join(rkeys)); // all t : Time, r : Room | r.current.t in r.keys 
		Formula x32=(rt1.and(rt2).and(rt3)).forAll(r.oneOf(room).and(t.oneOf(time))); 

		Formula t11 = time_next_.totalOrder(time, time_init, time_end);
		Formula t22 = time_next.eq(time_next_.union(time_loop)); // next = next_ + loop
		Formula t33 = time_loop.one(); // one loop
		Formula t4 = time_loop.join(time).eq(time_end); // loop.Time = end
		Formula time = t11.and(t22).and(t33).and(t4);

		return Formula.compose(FormulaOperator.AND, x22, x27, x32, x60, x86, time);
	}

	private Formula init() {
		Variable r=Variable.unary("r");
		Formula x158=r.join(lastkey.join(time_init)).eq(r.join(current.join(time_init)));
		Formula x111=x158.forAll(r.oneOf(room)); // all r : Room | r.lastkey.init = r.current.init

		Formula x149=(guest.join(gkeys.join(time_init))).no(); // no Guest.gkeys.init
		Formula x152=(occupant.join(time_init)).no(); // no occupant.init

		return x111.and(x149).and(x152);
	}

	private Formula next() {
		Variable t=Variable.unary("t");
		Expression x167=time_init.join(time_next.closure().union(Expression.IDEN.intersection(time.product(time))));
		Variable g=Variable.unary("g");
		Variable r=Variable.unary("r");
		Variable k=Variable.unary("k");

		Formula x189=entry(t,r,k,g).or(checkout(t,g)).or(checkin(t,r,k,g));
		Formula x181=x189.forSome((g.oneOf(guest)).and(r.oneOf(room)).and(k.oneOf(key)));
		Formula next=x181.forAll(t.oneOf(x167));
		return next;
	}

	private Formula noIntervenes() {
		Variable t=Variable.unary("t");
		Variable g=Variable.unary("g");
		Variable r=Variable.unary("r");
		Variable k=Variable.unary("k");

		Formula checkin = checkin(t,r,k,g);
		Formula entry = ((t.join(time_next)).some()).and(entry(t.join(time_next), r, k, g));

		Formula x394=checkin.implies(entry);

		Formula x386=x394.forAll(g.oneOf(guest).and(r.oneOf(room)).and(k.oneOf(key)));
		Formula x378=x386.forAll(t.oneOf(time_init.join((time_next.closure()).union(Expression.IDEN.intersection(time.product(time))))));
		return x378;
	}

	private Formula noBadEntries() {
		Variable t=Variable.unary("t");
		Variable r=Variable.unary("r");
		Variable g=Variable.unary("g");
		Variable k=Variable.unary("k");

		Formula entry = entry(t,r,k,g);

		Formula x653=r.join(occupant.join(t)).some(); // some r.occupant.t

		Formula x624=(g.in(r.join(occupant.join(t)))); // g in r.occupant.t

		Formula x574=(entry.and(x653)).implies(x624);

		Formula x566=x574.forAll((r.oneOf(room)).and(g.oneOf(guest)).and(k.oneOf(key)));
		Formula x558=x566.forAll(t.oneOf(time_init.join((time_next.closure()).union(Expression.IDEN.intersection(time.product(time))))));

		return x558;
	}

	private Formula entry(Expression t, Variable r, Variable k, Variable g) {
		Formula x583=k.eq(r.join(current.join(t))); // k = r.current.t

		Expression x595=((r.join(current.join(t))).join(key_next.closure())).intersection(r.join(rkeys)); // (r.current.t).next+ & r.keys
		Formula x593=k.eq(x595.difference(x595.join(key_next.closure()))); // k = (r.current.t).next+ & r.keys - ((r.current.t).next+ & r.keys).next+
		Formula x581=x583.or(x593);

		Formula x576=k.in(g.join(gkeys.join(t))); // k in g.keys.t
		Formula x609=(r.join(current.join(t.join(time_next)))).eq(k); // r.current.t' = k

		Variable r1=Variable.unary("r'");
		Formula x641=(r1.join(current.join(t))).eq(r1.join(current.join(t.join(time_next))));
		Formula x637=x641.forAll(r1.oneOf(room.difference(r))); // all x : Room - r | x.current.t = x.current.t'

		Formula x614=gkeys.join(t).eq(gkeys.join(t.join(time_next))); // gkeys.t = gkeys.t'
		Formula x629=(lastkey.join(t)).eq(lastkey.join(t.join(time_next))); // lastley.t = lastkey.t'
		Formula x647=(occupant.join(t)).eq(occupant.join(t.join(time_next))); // occupant.t = occupant.t'
		Formula entry = Formula.compose(FormulaOperator.AND, x576, x581, x614, x629, x637, x647, x609);
		return entry;
	}

	private Formula checkin(Variable t, Variable r, Variable k, Variable g) {
		Formula x398=g.join(gkeys.join(t.join(time_next))).eq((g.join(gkeys.join(t))).union(k)); // g.keys.t' = g.keys.t + k
		Formula x407=(r.join(occupant.join(t))).no(); // no r.occupant.t
		Formula x411=(lastkey.join(t.join(time_next))).eq((lastkey.join(t)).override(r.product(k))); // lastkey.t' = lastkey.t ++ r -> k
		Expression x428=(((r.join(lastkey.join(t))).join(key_next.closure())).intersection(r.join(rkeys))).join(key_next.closure());
		Expression x420=(((r.join(lastkey.join(t))).join(key_next.closure())).intersection(r.join(rkeys))).difference(x428);
		Formula x419=k.eq(x420); // k = (r.lastkey.t.next+ & r.keys) - (r.lastkey.t.next+ & r.keys).next+
		Formula x439=(occupant.join(t.join(time_next))).eq((occupant.join(t)).union(r.product(g))); // occupant.t' = occupant.t + r -> g
		Formula x447=(current.join(t)).eq(current.join(t.join(time_next))); // current.t = current.t'
		Variable g1=Variable.unary("g1");
		Formula x461=(g1.join(gkeys.join(t))).eq(g1.join(gkeys.join(t.join(time_next))));
		Formula x457=x461.forAll(g1.oneOf(guest.difference(g))); // all g1 : Guest - g | g.keys.t = g.keys.t'
		Formula checkin=Formula.compose(FormulaOperator.AND, x398, x407, x411, x419, x439, x447, x457);
		return checkin;
	}

	private Formula checkout(Variable t, Variable g) {
		Formula x337=((occupant.join(t)).join(g)).some(); // some (occupant.t).g
		Formula x343=occupant.join(t.join(time_next)).eq((occupant.join(t)).difference(room.product(g))); // occupant.t' = occupant.t - room -> g
		Formula x351=(current.join(t)).eq(current.join(t.join(time_next))); // current.t = current.t'
		Formula x352=(gkeys.join(t)).eq(gkeys.join(t.join(time_next))); // lastkey.t = lastkey.t'
		Formula x353=(lastkey.join(t)).eq(lastkey.join(t.join(time_next))); // gkeys.t = gkeys.t'
		Formula checkout = x337.and(x343.and(x351)).and(x352).and(x353);
		return checkout;
	}

	@Override
	public int getBitwidth() {
		return 1;
	}

	@Override
	public String shortName() {
		return "Hotel "+n+" "+t+" "+variant.name();
	}






}
