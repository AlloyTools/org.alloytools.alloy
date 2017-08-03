module tests/test49 -- example created by Daniel Jackson

open util/ordering[Time] as time

sig Key {issued: set Time}
sig Time {}

sig Card {k1, k2: Key}
sig Room {
    k1, k2: Key one -> Time,
    prev:  Key lone -> Time,
    occ: Guest -> Time
    }
   {
    occ.canChangeIn [Checkin + Checkout]
    }

sig Guest {
    holds: Card -> Time
    }

pred init (t: Time) {
    prev.t = k2.t
    (k1 + k2).t in Room lone -> Key
    issued.t = Room.(k1+k2).t
    no holds.t and no occ.t
    }

abstract sig HotelEvent {
    pre, post: Time,
    guest: Guest
    }

abstract sig RoomCardEvent extends HotelEvent {
    room: Room,
    card: Card
    }

sig Checkin extends RoomCardEvent { }
    {
    no room.occ.pre
    card.k1 = room.prev.pre
    card.k2 not in issued.pre
    holds.post = holds.pre + guest -> card
    issued.post = issued.pre + card.k2
    prev.post = prev.pre ++ room -> card.k2
    occ.post = occ.pre + room -> guest
    }

abstract sig Enter extends RoomCardEvent { }
    {
    card in guest.holds.pre
    }

sig NormalEnter extends Enter { }
    {
    card.k1 = room.k1.pre
    card.k2 = room.k2.pre
    }

sig RecodeEnter extends Enter { }
    {
    card.k1 = room.k2.pre
    k1.post = k1.pre ++ room -> card.k1
    k2.post = k2.pre ++ room -> card.k2
    }

sig Checkout extends HotelEvent { }
    {
    some occ.pre.guest
    occ.post = occ.pre - Room -> guest
    }

fact {
    occ.canChangeIn [Checkin + Checkout]

            (Checkin + Checkout).allows [occ]
}

pred allows (he: HotelEvent, field: univ -> univ -> Time) {
    all e: HotelEvent | field.(e.pre) = field.(e.post) or e in he
    }
pred canChangeIn (field: univ -> univ -> Time, events: set HotelEvent) {
    all e: HotelEvent | field.(e.pre) = field.(e.post) or e in events
    }
pred allows (he: HotelEvent, field: univ -> Time) {
    all e: HotelEvent | field.(e.pre) = field.(e.post) or e in he
    }
pred canChangeIn (field: univ -> Time, events: set HotelEvent) {
    all e: HotelEvent | field.(e.pre) = field.(e.post) or e in events
    }

fact Traces {
    first.init

    all t: Time - last | let t' = t.next |
        some e: HotelEvent {
            e.pre = t and e.post = t'

            (Checkin+Checkout).allows [occ]

            k1.t = k1.t' and k2.t = k2.t' or e in RecodeEnter
            (Room<:prev).t = prev.t' and issued.t = issued.t' and holds.t = holds.t' or e in Checkin
            occ.t = occ.t' or e in Checkin + Checkout
            }
    }

run {some Checkout} expect 1

assert NoBadEntry {
    all e: Enter | let occs = occ.(e.pre) [e.room] |
        some occs => e.guest in occs
--      e.guest in occs
    }
check NoBadEntry for 3 but 2 Room, 2 Guest, 5 Time, 4 HotelEvent expect 0
check NoBadEntry for 5 expect 0
check NoBadEntry for 3 but 7 Key, 4 Card, 1 Room, 2 Guest, 7 Time, 6 HotelEvent expect 0
check NoBadEntry for 3 but 2 Room, 2 Guest, 6 Time, 5 HotelEvent expect 0

fact NoIntervening {
    all c: Checkin - pre.last |
        some e: Enter | e.pre = c.post and e.room = c.room and e.guest = c.guest
    }
