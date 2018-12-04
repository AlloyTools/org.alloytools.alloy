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


assert WriteIdempotent{
	all m, m_, m__: Memory, a: Addr, d: Data |
		write [m, m_, a, d] and write [m_, m__, a, d] => m_ = m__
	}
check WriteIdempotent for 16

assert WriteRead {
	all m, m_: Memory, a: Addr, d1, d2: Data |
		write [m, m_, a, d1] and read [m_, a, d2] => d1 = d2
	}
check WriteRead for 16