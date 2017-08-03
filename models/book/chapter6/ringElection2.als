module chapter6/ringElection2 --- the final version (as depicted in Fig 6.1)

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

pred progress  {
	all t: Time - TO/last |
		let t' = TO/next [t] |
			some Process.toSend.t => some p: Process | not skip [t, t', p]
	}

assert AtLeastOneElected { progress => some elected.Time }
check AtLeastOneElected for 3 Process, 7 Time
// This should not find any counterexample

pred looplessPath { no disj t, t': Time | toSend.t = toSend.t' }

// This produces an instance
run looplessPath for 3 Process, 12 Time

// This does not produce an instance
run looplessPath for 3 Process, 13 Time

// Therefore, we can conclude that a scope of 12 for Time is
// sufficient to reach all states of the protocol for a three-node ring.
