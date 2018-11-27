module chapter6/memory/abstractMemory [Addr, Data]



sig Memory {
	data: Addr -> lone Data
	}

pred init [m: Memory] {
	no m.data
	}

pred write [m, m_: Memory, a: Addr, d: Data] {
	m_.data = m.data + a -> d
	}

pred read [m: Memory, a: Addr, d: Data] {
	let d_ = m.data [a] | some d_ implies d = d_
	}

fact Canonicalize {
	//no disj m, m_: Memory | m.data = m_.data
    all m, m_: Memory | m != m_ implies m.data != m_.data
	}

// This command should not find any counterexample
assert WriteIdempotent{
	all m, m_, m__: Memory, a: Addr, d: Data |
		write [m, m_, a, d] and write [m_, m__, a, d] => m_ = m__
	}
check WriteIdempotent for 16
