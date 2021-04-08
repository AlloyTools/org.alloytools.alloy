open util/ordering[Id]

sig Node {
	id : one Id,
	succ : one Node,
	var inbox : set Id,
	var outbox : set Id
}

sig Id {}

fact ring {
	all i : Id | lone id.i
	all n : Node | Node in n.^succ
}

fun elected : set Node {
	{n : Node | once (n.id in n.inbox)}
}

pred send [n : Node] {
	some i : n.outbox {
		n.outbox' = n.outbox - i
		n.succ.inbox' = n.succ.inbox + i
	}
	all m : Node - n.succ | m.inbox' = m.inbox
	all m : Node - n | m.outbox' = m.outbox
}

pred compute [n : Node] {
	some i : n.inbox {
		n.inbox' = n.inbox - i
		n.outbox' = n.outbox + (i - n.id.*(~next))
	}
	all m : Node - n | m.inbox' = m.inbox
	all m : Node - n | m.outbox' = m.outbox
}

pred skip {
	inbox' = inbox
	outbox' = outbox
}

fact init {
	no inbox
	outbox = id
}

fact transitions {
	always (skip or some n : Node | send[n] or compute[n])
}

run {} for 4 but exactly 4 Node, 10 steps
run example {eventually some elected} for 3 but exactly 3 Node, 6 steps

assert safety {
	always lone elected
}
check safety for 3 but 15 steps


pred sendEnabled [n : Node] {
	some n.outbox
}

pred computeEnabled [n : Node] {
	some n.inbox
}

pred fairness {
	all n : Node {
		(eventually always sendEnabled[n] implies (always eventually send[n]))
		(eventually always computeEnabled[n] implies (always eventually compute[n]))
	}
}

assert liveness {
	eventually some elected
//	fairness implies eventually some elected
//	fairness and some Node implies eventually some elected
}
check liveness for 3
