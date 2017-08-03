module chapter6/memory/abstractMemory [Addr, Data] ----- the model from page 217

sig Memory {
	data: Addr -> lone Data
	}

pred init [m: Memory] {
	no m.data
	}

pred write [m, m': Memory, a: Addr, d: Data] {
	m'.data = m.data ++ a -> d
	}

pred read [m: Memory, a: Addr, d: Data] {
	let d' = m.data [a] | some d' implies d = d'
	}

fact Canonicalize {
	no disj m, m': Memory | m.data = m'.data
	}

// This command should not find any counterexample
WriteRead: check {
	all m, m': Memory, a: Addr, d1, d2: Data |
		write [m, m', a, d1] and read [m', a, d2] => d1 = d2
	}

// This command should not find any counterexample
WriteIdempotent: check {
	all m, m', m": Memory, a: Addr, d: Data |
		write [m, m', a, d] and write [m', m", a, d] => m' = m"
	}
