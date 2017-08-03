module chapter5/sets2 ----- page 157

sig Set {
	elements: set Element
}

sig Element {}

assert Closed {
	all s0, s1: Set |
		some s2: Set |
			s2.elements = s0.elements + s1.elements
	}

fact SetGenerator {
	some s: Set | no s.elements
	all s: Set, e: Element | some s': Set | s'.elements = s.elements + e
	}

// This check should not produce a counterexample
check Closed for 4 Element, 16 Set
