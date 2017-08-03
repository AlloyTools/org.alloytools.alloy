module chapter6/ringElection1 --- the version up to the top of page 181

open util/ordering[Time] as TO
open util/ordering[Process] as PO

sig Time {}

sig Process {
	succ: Process,
	toSend: Process -> Time,
	elected: set Time
	}

fact ring {
	all p: Process | Process in p.^succ
	}

pred init [t: Time] {
	all p: Process | p.toSend.t = p
	}

pred step [t, t': Time, p: Process] {
	let from = p.toSend, to = p.succ.toSend |
		some id: from.t {
			from.t' = from.t - id
			to.t' = to.t + (id - p.succ.prevs)
		}
	}

fact defineElected {
	no elected.first
	all t: Time-first | elected.t = {p: Process | p in p.toSend.t - p.toSend.(t.prev)}
	}

fact traces {
	init [first]
	all t: Time-last |
		let t' = t.next |
			all p: Process |
				step [t, t', p] or step [t, t', succ.p] or skip [t, t', p]
	}

pred skip [t, t': Time, p: Process] {
	p.toSend.t = p.toSend.t'
	}

pred show { some elected }
run show for 3 Process, 4 Time
// This generates an instance similar to Fig 6.4

assert AtMostOneElected { lone elected.Time }
check AtMostOneElected for 3 Process, 7 Time
// This should not find any counterexample

assert AtLeastOneElected { some t: Time | some elected.t }
check AtLeastOneElected for 3 Process, 7 Time
// This generates a counterexample in which nothing happens
