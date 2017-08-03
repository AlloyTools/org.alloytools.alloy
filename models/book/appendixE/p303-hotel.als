module hotel

open util/ordering [Time] as timeOrder

sig Key, Time {}

sig Card {
	fst, snd: Key
	}

sig Room {
	key: Key one->Time
	}

one sig Desk {
	issued: Key->Time,
	prev: (Room->lone Key)->Time
	}

sig Guest {
	cards: Card->Time
	}

pred init [t: Time] {
	Desk.prev.t = key.t
	Desk.issued.t = Room.key.t and no cards.t
	}

pred checkin [t,t': Time, r: Room, g: Guest] {
	some c: Card {
		c.fst = r.(Desk.prev.t)
		c.snd not in Desk.issued.t
		cards.t' = cards.t + g->c ------------- bug! (see page 306)
		Desk.issued.t' = Desk.issued.t + c.snd
		Desk.prev.t' = Desk.prev.t ++ r->c.snd
		}
	key.t = key.t'
	}

pred enter [t,t': Time, r: Room, g: Guest] {
	some c: g.cards.t |
		let k = r.key.t {
			c.snd = k and key.t' = key.t
			or c.fst = k and key.t' = key.t ++ r->c.snd
			}
	issued.t = issued.t' and (Desk<:prev).t = prev.t'
	cards.t = cards.t'
	}

fact Traces {
	init [first]
	all t: Time - last | some g: Guest, r: Room |
		checkin [t, t.next, r, g] or enter[t, t.next, r, g]
	}

assert NoIntruder {
	no t1: Time, g: Guest, g': Guest-g, r: Room |
		let t2=t1.next, t3=t2.next, t4=t3.next {
			enter [t1, t2, r, g]
			enter [t2, t3, r, g']
			enter [t3, t4, r, g]
		}
	}

-- This check now succeeds without finding any counterexample.
check NoIntruder for 3 but 6 Time, 1 Room, 2 Guest

-- To increase our confidence, we can increase the scope.
-- This time, it finds a counterexample.
check NoIntruder for 4 but 7 Time, 1 Room, 2 Guest
