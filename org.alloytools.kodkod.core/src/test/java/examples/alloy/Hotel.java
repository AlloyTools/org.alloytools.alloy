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
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Proof;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.ucore.RCEStrategy;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.Universe;
import kodkod.util.nodes.Nodes;
import kodkod.util.nodes.PrettyPrinter;

/**
 * Encodes the hotel example.
 *
 * @author Emina Torlak
 */
public final class Hotel {

    private final Relation Time, Event, first, last;
    private final Relation pre, post, next;

    private final Relation Key, Card, Room, Guest, HotelEvent, RoomCardEvent, Checkin, Enter, NormalEnter, RecodeEnter,
                    Checkout;

    private final Relation guest, room, card, k1, k2;
    private final Relation key, prev, occ, holds;

    /**
     * Constructs a new instance of the hotel problem.
     */
    public Hotel() {
        this.Time = Relation.unary("Time");
        this.Event = Relation.unary("Event");
        this.first = Relation.unary("first");
        this.last = Relation.unary("last");
        this.pre = Relation.binary("pre");
        this.post = Relation.binary("post");
        this.next = Relation.binary("next");

        this.Key = Relation.unary("Key");
        this.Card = Relation.unary("Card");
        this.Guest = Relation.unary("Guest");
        this.Room = Relation.unary("Room");
        this.HotelEvent = Relation.unary("HotelEvent");
        this.RoomCardEvent = Relation.unary("RoomCardEvent");
        this.Checkin = Relation.unary("Checkin");
        this.Enter = Relation.unary("Enter");
        this.NormalEnter = Relation.unary("NormalEnter");
        this.RecodeEnter = Relation.unary("RecodeEnter");
        this.Checkout = Relation.unary("Checkout");

        this.key = Relation.ternary("key");
        this.prev = Relation.ternary("prev");
        this.occ = Relation.ternary("occ");
        this.holds = Relation.ternary("holds");

        this.guest = Relation.binary("guest");
        this.room = Relation.binary("room");
        this.card = Relation.binary("card");
        this.k1 = Relation.binary("k1");
        this.k2 = Relation.binary("k2");
    }

    /**
     * Returns the invariants for the Time and Event signatures and their fields.
     *
     * @return invariants for the Time and Event signatures and their fields.
     */
    public Formula timeEventInvariants() {
        final List<Formula> invs = new ArrayList<Formula>();

        invs.add(next.totalOrder(Time, first, last));
        invs.add(pre.function(Event, Time));
        invs.add(post.function(Event, Time));

        final Variable t = Variable.unary("t");
        final Variable e = Variable.unary("e");

        // all t: Time - last | one e: Event | e.pre = t and e.post = t.next
        final Formula f0 = e.join(pre).eq(t).and(e.join(post).eq(t.join(next)));
        final Formula f1 = f0.comprehension(e.oneOf(Event)).one();
        invs.add(f1.forAll(t.oneOf(Time.difference(last))));

        return Formula.and(invs);
    }

    /**
     * Returns the "unchanged" predicate for the given event expression and field.
     *
     * @return "unchanged" predicate for the given event expression and field.
     */
    public Formula unchanged(Expression e, Expression field) {
        // field.(this.pre) = field.(this.post)
        return field.join(e.join(pre)).eq(field.join(e.join(post)));
    }

    /**
     * Returns the "modifes" predicate for the given event expression and field.
     *
     * @return "modifies" predicate for the given event expression and field.
     */
    public Formula modifies(Expression es, Expression field) {
        // all e: Event -es | field.(e.pre) = field.(e.post)
        final Variable e = Variable.unary("e");
        return field.join(e.join(pre)).eq(field.join(e.join(post))).forAll(e.oneOf(Event.difference(es)));
    }

    /**
     * Returns the invariants for Card and its fields.
     *
     * @return invariants for Card and its fields.
     */
    public Formula cardInvariants() {
        return k1.function(Card, Key).and(k2.function(Card, Key));
    }

    /**
     * Returns the invariants for Room and its fields.
     *
     * @return invariants for Room and its fields.
     */
    public Formula roomInvariants() {
        // key: Key one -> Time,
        // prev: Key lone -> Time,
        // occ: Guest -> Time

        final List<Formula> invs = new ArrayList<Formula>();

        invs.add(key.in(Room.product(Key).product(Time)));
        invs.add(prev.in(Room.product(Key).product(Time)));
        invs.add(occ.in(Room.product(Guest).product(Time)));

        final Variable r = Variable.unary("r");
        final Variable t = Variable.unary("t");

        // all r: Room, t: Time | one r.key.t
        invs.add(r.join(key).join(t).one().forAll(r.oneOf(Room).and(t.oneOf(Time))));

        // all r: Room, t: Time | lone r.prev.t
        invs.add(r.join(prev).join(t).lone().forAll(r.oneOf(Room).and(t.oneOf(Time))));

        return Formula.and(invs);
    }

    /**
     * Returns the invariants for Guest and its fields.
     *
     * @return invariants for Guest and its fields.
     */
    public Formula guestInvariants() {
        // holds: Card -> Time
        return holds.in(Guest.product(Card).product(Time));
    }

    /**
     * Returns the invariants for HotelEvent and its fields.
     *
     * @return invariants for HotelEvent and its fields.
     */
    public Formula hotelEventInvariants() {
        // abstract sig HotelEvent extends Event {
        // guest: Guest
        // }
        final List<Formula> invs = new ArrayList<Formula>();
        invs.add(HotelEvent.eq(Event));
        invs.add(HotelEvent.eq(RoomCardEvent.union(Checkout)));
        invs.add(RoomCardEvent.intersection(Checkout).no());
        invs.add(guest.function(HotelEvent, Guest));

        return Formula.and(invs);
    }

    /**
     * Returns the invariants for RoomCardEvent and its fields.
     *
     * @return invariants for RoomCardEvent and its fields.
     */
    public Formula roomCardInvariants() {
        // abstract sig RoomCardEvent extends HotelEvent {
        // room: Room,
        // card: Card
        // }
        final List<Formula> invs = new ArrayList<Formula>();
        invs.add(RoomCardEvent.in(HotelEvent));
        invs.add(RoomCardEvent.eq(Checkin.union(Enter)));
        invs.add(Checkin.intersection(Enter).no());

        invs.add(room.function(RoomCardEvent, Room));
        invs.add(card.function(RoomCardEvent, Card));

        return Formula.and(invs);
    }

    /** @return e.room */
    Expression room(Expression e) {
        return e.join(room);
    }

    /** @return e.card */
    Expression card(Expression e) {
        return e.join(card);
    }

    /** @return e.pre */
    Expression pre(Expression e) {
        return e.join(pre);
    }

    /** @return e.post */
    Expression post(Expression e) {
        return e.join(post);
    }

    /** @return e.guest */
    Expression guest(Expression e) {
        return e.join(guest);
    }

    /**
     * Returns the invariants for Checkin and its fields.
     *
     * @return invariants for Checkin and its fields.
     */
    public Formula invsForCheckin() {
        // sig Checkin extends RoomCardEvent { }
        // {
        // no room.occ.pre
        // card.k1 = room.prev.pre
        // holds.post = holds.pre + guest -> card
        // prev.post = prev.pre ++ room -> card.k2
        // occ.post = occ.pre + room -> guest
        //
        // key.unchanged
        // }

        final List<Formula> invs = new ArrayList<Formula>();

        invs.add(Checkin.in(RoomCardEvent));

        final Variable c = Variable.unary("c");

        // no room.occ.pre
        invs.add(room(c).join(occ).join(pre(c)).no().forAll(c.oneOf(Checkin)));

        // card.k1 = room.prev.pre
        invs.add(card(c).join(k1).eq(room(c).join(prev).join(pre(c))).forAll(c.oneOf(Checkin)));

        // holds.post = holds.pre + guest -> card
        invs.add(holds.join(post(c)).eq(holds.join(pre(c)).union(guest(c).product(card(c)))).forAll(c.oneOf(Checkin)));

        // prev.post = prev.pre ++ room -> card.k2
        invs.add(prev.join(post(c)).eq(prev.join(pre(c)).override(room(c).product(card(c).join(k2)))).forAll(c.oneOf(Checkin)));

        // occ.post = occ.pre + room -> guest
        invs.add(occ.join(post(c)).eq(occ.join(pre(c)).union(room(c).product(guest(c)))).forAll(c.oneOf(Checkin)));

        invs.add(unchanged(c, key).forAll(c.oneOf(Checkin)));
        return Formula.and(invs);
    }

    /**
     * Returns the invariants for Enter and its fields.
     *
     * @return invariants for Enter and its fields.
     */
    public Formula enterInvariants() {
        // abstract sig Enter extends RoomCardEvent { }
        // {
        // card in guest.holds.pre
        // }

        final List<Formula> invs = new ArrayList<Formula>();
        invs.add(Enter.in(RoomCardEvent));
        invs.add(Enter.eq(NormalEnter.union(RecodeEnter)));
        invs.add(NormalEnter.intersection(RecodeEnter).no());

        final Variable e = Variable.unary("e");
        invs.add(card(e).in(guest(e).join(holds).join(pre(e))).forAll(e.oneOf(Enter)));

        return Formula.and(invs);
    }

    /**
     * Returns the invariants for NormalEnter and its fields.
     *
     * @return invariants for NormalEnter and its fields.
     */
    public Formula normalEnterInvariants() {
        // sig NormalEnter extends Enter { }
        // {
        // card.k2 = room.key.pre
        //
        // prev.unchanged
        // holds.unchanged
        // occ.unchanged
        // key.unchanged
        // }

        final List<Formula> invs = new ArrayList<Formula>();
        invs.add(NormalEnter.in(Enter));

        final Variable n = Variable.unary("n");
        invs.add(card(n).join(k2).eq(room(n).join(key).join(pre(n))).forAll(n.oneOf(NormalEnter)));
        invs.add(unchanged(n, prev).forAll(n.oneOf(NormalEnter)));
        invs.add(unchanged(n, holds).forAll(n.oneOf(NormalEnter)));
        invs.add(unchanged(n, occ).forAll(n.oneOf(NormalEnter)));
        invs.add(unchanged(n, key).forAll(n.oneOf(NormalEnter)));

        return Formula.and(invs);
    }

    /**
     * Returns the invariants for RecodeEnter and its fields.
     *
     * @return invariants for RecodeEnter and its fields.
     */
    public Formula recodeEnterInvariants() {
        // sig RecodeEnter extends Enter { }
        // {
        // card.k1 = room.key.pre
        // key.post = key.pre ++ room -> card.k2
        //
        // prev.unchanged
        // holds.unchanged
        // occ.unchanged
        // }

        final List<Formula> invs = new ArrayList<Formula>();
        invs.add(RecodeEnter.in(Enter));

        final Variable r = Variable.unary("n");
        invs.add(card(r).join(k1).eq(room(r).join(key).join(pre(r))).forAll(r.oneOf(RecodeEnter)));
        invs.add(key.join(post(r)).eq(key.join(pre(r)).override(room(r).product(card(r).join(k2)))).forAll(r.oneOf(RecodeEnter)));

        invs.add(unchanged(r, prev).forAll(r.oneOf(RecodeEnter)));
        invs.add(unchanged(r, holds).forAll(r.oneOf(RecodeEnter)));
        invs.add(unchanged(r, occ).forAll(r.oneOf(RecodeEnter)));

        return Formula.and(invs);
    }

    /**
     * Returns the invariants for Checkout and its fields.
     *
     * @return invariants for Checkout and its fields.
     */
    public Formula invsForCheckout() {
        // sig Checkout extends HotelEvent { }
        // {
        // some occ.pre.guest
        //
        // -- DNJ: can comment these out and still unsat
        // occ.post = occ.pre - Room -> guest
        // prev.unchanged
        // holds.unchanged
        // key.unchanged
        // }

        final List<Formula> invs = new ArrayList<Formula>();
        invs.add(Checkout.in(HotelEvent));

        final Variable c = Variable.unary("n");
        invs.add(occ.join(pre(c)).join(guest(c)).some().forAll(c.oneOf(Checkout)));
        invs.add(occ.join(post(c)).eq(occ.join(pre(c)).difference(Room.product(guest(c)))).forAll(c.oneOf(Checkout)));

        invs.add(unchanged(c, prev).forAll(c.oneOf(Checkout)));
        invs.add(unchanged(c, holds).forAll(c.oneOf(Checkout)));
        invs.add(unchanged(c, key).forAll(c.oneOf(Checkout)));

        return Formula.and(invs);
    }

    /**
     * Returns FreshIssue fact.
     *
     * @return FressIssue fact.
     */
    public Formula freshIssue() {
        // -- don't issue same key twice
        // all disj e1, e2: Checkin | e1.card.k2 != e2.card.k2
        // -- don't issue key initially installed in lock
        // all e: Checkin | e.card.k2 !in Room.key.first

        final List<Formula> invs = new ArrayList<Formula>();

        final Variable e1 = Variable.unary("e1");
        final Variable e2 = Variable.unary("e2");
        final Variable e = Variable.unary("e");

        invs.add(e1.eq(e2).not().implies(e1.join(card).join(k2).eq(e2.join(card).join(k2)).not()).forAll(e1.oneOf(Checkin).and(e2.oneOf(Checkin))));
        invs.add(e.join(card).join(k2).in(Room.join(key).join(first)).not().forAll(e.oneOf(Checkin)));

        return Formula.and(invs);

    }

    /**
     * Returns init fact.
     *
     * @return init fact.
     */
    public Formula initInvariant() {
        // pred init (t: Time) {
        // prev.t = key.t
        // key.t in Room lone -> Key
        // no holds.t and no occ.t
        // }
        // fact {first.init}

        final List<Formula> invs = new ArrayList<Formula>();

        invs.add(prev.join(first).eq(key.join(first)));
        invs.add(key.join(first).in(Room.product(Key)));
        final Variable k = Variable.unary("k");
        invs.add(key.join(first).join(k).lone().forAll(k.oneOf(Key)));
        invs.add(holds.join(first).no());
        invs.add(occ.join(first).no());

        return Formula.and(invs);
    }

    /**
     * Returns the noIntervening fact.
     *
     * @return noIntervening fact.
     */
    public Formula noIntervening() {
        // fact NoIntervening {
        // all c: Checkin - pre.last |
        // some e: Enter | e.pre = c.post and e.room = c.room and e.guest =
        // c.guest
        // }
        final Variable c = Variable.unary("c");
        final Variable e = Variable.unary("e");
        final Formula f = e.join(pre).eq(c.join(post)).and(e.join(room).eq(c.join(room))).and(e.join(guest).eq(c.join(guest)));
        return f.forSome(e.oneOf(Enter)).forAll(c.oneOf(Checkin.difference(pre.join(last))));
    }

    /**
     * Returns NoBadEntry formula.
     *
     * @return NoBadEntry formula.
     */
    public Formula noBadEntry() {
        // all e: Enter | let occs = occ.(e.pre) [e.room] |
        // some occs => e.guest in occs

        final Variable e = Variable.unary("e");
        final Expression occs = e.join(room).join(occ.join(e.join(pre)));

        return occs.some().implies(e.join(guest).in(occs)).forAll(e.oneOf(Enter));
    }

    /**
     * Returns the conjunction of all invariants.
     *
     * @return conjunction of all invariants.
     */
    public Formula invariants() {
        final List<Formula> invs = new ArrayList<Formula>();

        invs.add(timeEventInvariants());

        invs.add(cardInvariants());
        invs.add(roomInvariants());
        invs.add(guestInvariants());

        invs.add(initInvariant());

        invs.add(hotelEventInvariants());

        invs.add(roomCardInvariants());
        invs.add(invsForCheckin());

        invs.add(enterInvariants());
        invs.add(normalEnterInvariants());
        invs.add(recodeEnterInvariants());

        invs.add(invsForCheckout());

        invs.add(freshIssue());

        invs.add(noIntervening());
        return Formula.and(invs);
    }

    /**
     * Returns the assertion "check noBadEntry"
     *
     * @return invariants() && !oBadEntry()
     */
    public Formula checkNoBadEntry() {
        return invariants().and(noBadEntry().not());
    }

    /**
     * Returns bounds for the given number of times, events, rooms, cards, keys and
     * guests.
     *
     * @return bounds for the given scopes.
     */
    public Bounds bounds(int t, int e, int r, int c, int k, int g) {
        final Relation[] tops = {
                                 Time, Event, Room, Card, Key, Guest
        };
        final int[] scopes = {
                              t, e, r, c, k, g
        };

        final List<String> atoms = new ArrayList<String>();
        for (int i = 0; i < tops.length; i++) {
            Relation top = tops[i];
            for (int j = 0, scope = scopes[i]; j < scope; j++)
                atoms.add(top.name() + j);
        }

        final Universe u = new Universe(atoms);
        final TupleFactory f = u.factory();
        final Bounds b = new Bounds(u);

        for (int i = 0; i < tops.length; i++) {
            Relation top = tops[i];
            b.bound(top, f.range(f.tuple(top.name() + 0), f.tuple(top.name() + (scopes[i] - 1))));
        }

        b.bound(first, b.upperBound(Time));
        b.bound(last, b.upperBound(Time));
        b.bound(next, b.upperBound(Time).product(b.upperBound(Time)));

        b.bound(pre, b.upperBound(Event).product(b.upperBound(Time)));
        b.bound(post, b.upperBound(Event).product(b.upperBound(Time)));

        b.bound(HotelEvent, b.upperBound(Event));
        b.bound(RoomCardEvent, b.upperBound(Event));
        b.bound(Enter, b.upperBound(Event));
        b.bound(NormalEnter, b.upperBound(Event));
        b.bound(RecodeEnter, b.upperBound(Event));
        b.bound(Checkin, b.upperBound(Event));
        b.bound(Checkout, b.upperBound(Event));

        b.bound(k1, b.upperBound(Card).product(b.upperBound(Key)));
        b.bound(k2, b.upperBound(Card).product(b.upperBound(Key)));

        b.bound(key, b.upperBound(Room).product(b.upperBound(Key)).product(b.upperBound(Time)));
        b.bound(prev, b.upperBound(Room).product(b.upperBound(Key)).product(b.upperBound(Time)));
        b.bound(occ, b.upperBound(Room).product(b.upperBound(Guest)).product(b.upperBound(Time)));

        b.bound(holds, b.upperBound(Guest).product(b.upperBound(Card)).product(b.upperBound(Time)));

        b.bound(guest, b.upperBound(HotelEvent).product(b.upperBound(Guest)));

        b.bound(room, b.upperBound(RoomCardEvent).product(b.upperBound(Room)));
        b.bound(card, b.upperBound(RoomCardEvent).product(b.upperBound(Card)));

        return b;
    }

    /**
     * Returns bounds for the given scope.
     *
     * @return bounds for the given scope.
     */
    public Bounds bounds(int n) {
        return bounds(n, n, n, n, n, n);
    }

    private static void usage() {
        System.out.println("java examples.Hotel [scope]");
        System.exit(1);
    }

    private static void checkMinimal(Set<Formula> core, Bounds bounds) {
        System.out.print("checking minimality ... ");
        final long start = System.currentTimeMillis();
        final Set<Formula> minCore = new LinkedHashSet<Formula>(core);
        Solver solver = new Solver();
        solver.options().setSolver(SATFactory.MiniSat);
        for (Iterator<Formula> itr = minCore.iterator(); itr.hasNext();) {
            Formula f = itr.next();
            Formula noF = Formula.TRUE;
            for (Formula f1 : minCore) {
                if (f != f1)
                    noF = noF.and(f1);
            }
            if (solver.solve(noF, bounds).instance() == null) {
                itr.remove();
            }
        }
        final long end = System.currentTimeMillis();
        if (minCore.size() == core.size()) {
            System.out.println("minimal (" + (end - start) + " ms).");
        } else {
            System.out.println("not minimal (" + (end - start) + " ms). The minimal core has these " + minCore.size() + " formulas:");
            for (Formula f : minCore) {
                System.out.println(" " + f);
            }
            // Solution sol = problem.solver.solve(Formula.and(minCore),
            // problem.bounds);
            // System.out.println(sol);
            // sol.proof().highLevelCore();
        }
    }

    /**
     * Usage: java examples.Hotel [scope]
     */
    public static void main(String[] args) {
        if (args.length < 1)
            usage();

        try {
            final int n = Integer.parseInt(args[0]);
            if (n < 1)
                usage();
            final Hotel model = new Hotel();
            final Solver solver = new Solver();
            solver.options().setSolver(SATFactory.MiniSatProver);
            solver.options().setLogTranslation(1);

            final Formula f = model.checkNoBadEntry();
            final Bounds b = model.bounds(n);

            // System.out.println(PrettyPrinter.print(f, 2, 100));

            final Solution sol = solver.solve(f, b);
            System.out.println(sol);

            if (sol.instance() == null) {
                final Proof proof = sol.proof();
                System.out.println("top-level formulas: " + proof.log().roots().size());
                System.out.println("initial core: " + proof.highLevelCore().size());
                System.out.print("\nminimizing core ... ");
                final long start = System.currentTimeMillis();
                proof.minimize(new RCEStrategy(proof.log()));
                final Set<Formula> core = Nodes.minRoots(f, proof.highLevelCore().values());
                final long end = System.currentTimeMillis();
                System.out.println("done (" + (end - start) + " ms).");
                System.out.println("minimal core: " + core.size());
                for (Formula u : core) {
                    System.out.println(PrettyPrinter.print(u, 2, 100));
                }
                checkMinimal(core, b);
            } else {
                System.out.println(sol);
            }
        } catch (NumberFormatException nfe) {
            usage();
        }
    }
}
