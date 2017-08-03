module chapter5/sets1 ----- page 156

sig Set {
	elements: set Element
}

sig Element {}

assert Closed {
	all s0, s1: Set |
		some s2: Set |
			s2.elements = s0.elements + s1.elements
	}

// This check should produce a counterexample
check Closed
