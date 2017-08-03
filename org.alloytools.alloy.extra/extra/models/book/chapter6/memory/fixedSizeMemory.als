module chapter6/memory/fixedSizeMemory [Addr, Data]

sig Memory {
	data: Addr -> one Data	
	}

pred init [m: Memory] {
	// This predicate is empty in order to allow non-deterministic initialization
	}

pred write [m, m': Memory, a: Addr, d: Data] {
	m'.data = m.data ++ a -> d
	}

pred read [m: Memory, a: Addr, d: Data] {
	d = m.data [a]
	}

fact Canonicalize {
	no disj m, m': Memory | m.data = m'.data
	}
