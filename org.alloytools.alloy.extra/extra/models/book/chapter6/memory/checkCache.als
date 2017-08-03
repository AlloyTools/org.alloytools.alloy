module chapter6/memory/checkCache [Addr, Data]

open chapter6/memory/cacheMemory [Addr, Data] as cache
open chapter6/memory/abstractMemory [Addr, Data] as amemory

fun alpha [c: CacheSystem]: Memory {
	{m: Memory | m.data = c.main ++ c.cache}
	}

// This check should not produce a counterexample
ReadOK: check {
	// introduction of m, m' ensures that they exist, and gives witnesses if counterexample
	all c: CacheSystem, a: Addr, d: Data, m: Memory |
		cache/read [c, a, d] and m = alpha [c] => amemory/read [m, a, d]
	}

// This check should not produce a counterexample
WriteOK: check {
	all c, c': CacheSystem, a: Addr, d: Data, m, m': Memory |
		cache/write [c, c', a, d] and m = alpha [c] and m' = alpha [c']
 			=> amemory/write [m, m', a, d]
	}

// This check should not produce a counterexample
LoadOK: check {
	all c, c': CacheSystem, m, m': Memory |
		cache/load [c, c'] and m = alpha [c] and m' = alpha [c'] => m = m'
	}

// This check should not produce a counterexample
FlushOK: check {
	all c, c': CacheSystem, m, m': Memory |
		cache/flush [c, c'] and m = alpha [c] and m' = alpha [c'] => m = m'
	}
