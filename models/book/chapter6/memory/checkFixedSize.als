module chapter6/memory/checkFixedSize [Addr, Data]

open chapter6/memory/fixedSizeMemory_H [Addr, Data] as fmemory
open chapter6/memory/abstractMemory [Addr, Data] as amemory

// define abstraction function from history-extended concrete state to abstract state
pred alpha [fm: fmemory/Memory_H, am: amemory/Memory] {
	am.data = fm.data - (fm.unwritten -> Data)
	}

// This check should not find a counterexample
initOk: check {
	all fm: fmemory/Memory_H, am: amemory/Memory |
		fmemory/init [fm] and alpha [fm, am] => amemory/init [am]
	}

// This check should not find a counterexample
readOk: check {
	all fm: fmemory/Memory_H, a: Addr, d: Data, am: amemory/Memory |
		fmemory/read [fm, a, d] and alpha [fm, am] => amemory/read [am, a, d]
	}

// This check should not find a counterexample
writeOk: check {
	all fm, fm': fmemory/Memory_H, a: Addr, d: Data, am, am': amemory/Memory |
		fmemory/write [fm, fm', a, d] and alpha [fm, am] and alpha [fm', am']
 		implies amemory/write [am, am', a, d]
	}
