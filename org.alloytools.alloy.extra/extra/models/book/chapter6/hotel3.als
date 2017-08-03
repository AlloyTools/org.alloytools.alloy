module chapter6/hotel3 --- model in Fig 6.10 without the NonIntervening fact

open util/ordering[Time] as to
open util/ordering[Key] as ko

sig Key, Time {}

sig Room {
	keys: set Key,
	currentKey: keys one -> Time
	}

fact {
	Room <: keys in Room lone -> Key
	}

one sig FrontDesk {
	lastKey: (Room -> lone Key) -> Time,
	occupant: (Room -> Guest) -> Time
	}

sig Guest {
	keys: Key -> Time
	}

fun nextKey [k: Key, ks: set Key]: set Key {
	min [k.nexts & ks]
	}

pred init [t: Time] {
	no Guest.keys.t
	no FrontDesk.occupant.t
	all r: Room | FrontDesk.lastKey.t [r] = r.currentKey.t
	}

abstract sig Event {
	pre, post: Time,
	guest: Guest
	}

abstract sig RoomKeyEvent extends Event {
	room: Room,
	key: Key
	}

sig Entry extends RoomKeyEvent { } {
	key in guest.keys.pre
	let ck = room.currentKey |
		(key = ck.pre and ck.post = ck.pre) or 
		(key = nextKey[ck.pre, room.keys] and ck.post = key)
	currentKey.post = currentKey.pre ++ room->key
	}

sig Checkin extends RoomKeyEvent { } {
	keys.post = keys.pre + guest -> key
	let occ = FrontDesk.occupant {
		no occ.pre [room]
		occ.post = occ.pre + room -> guest
		}
	let lk = FrontDesk.lastKey {
		lk.post = lk.pre ++ room -> key
		key = nextKey [lk.pre [room], room.keys]
		}
	}

sig Checkout extends Event { } {
	let occ = FrontDesk.occupant {
		some occ.pre.guest
		occ.post = occ.pre - Room -> guest
		}
	}

fact Traces {
	init [first]
	all t: Time-last |
		let t' = t.next |
			some e: Event {
				e.pre = t and e.post = t'
				currentKey.t != currentKey.t' => e in Entry
				occupant.t != occupant.t' => e in Checkin + Checkout
				(lastKey.t != lastKey.t' or keys.t != keys.t') => e in Checkin
			}
	}

assert NoBadEntry {
	all e: Entry |
		let o=FrontDesk.occupant.(e.pre) [e.room] | 
			some o => e.guest in o
	}

// This generates a counterexample similar to Fig 6.13
check NoBadEntry for 5 but 3 Room, 3 Guest, 5 Time, 4 Event
