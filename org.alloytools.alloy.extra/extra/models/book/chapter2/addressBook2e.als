module tour/addressBook2e --- this is the final model in Fig 2.14

abstract sig Target { }
sig Addr extends Target { }
abstract sig Name extends Target { }

sig Alias, Group extends Name { }

sig Book {
	names: set Name,
	addr: names->some Target
} {
	no n: Name | n in n.^addr
	all a: Alias | lone a.addr
}

pred add [b, b": Book, n: Name, t: Target] { b".addr = b.addr + n->t }
pred del [b, b": Book, n: Name, t: Target] { b".addr = b.addr - n->t }
fun lookup [b: Book, n: Name] : set Addr { n.^(b.addr) & Addr }

assert delUndoesAdd {
	all b, b", b"": Book, n: Name, t: Target |
		no n.(b.addr) and add [b, b", n, t] and del [b", b"", n, t]
		implies
		b.addr = b"".addr
}

// This should not find any counterexample.
check delUndoesAdd for 3

assert addIdempotent {
	all b, b", b"": Book, n: Name, t: Target |
		add [b, b", n, t] and add [b", b"", n, t]
		implies
		b".addr = b"".addr
}

// This should not find any counterexample.
check addIdempotent for 3

assert addLocal {
	all b, b": Book, n, n": Name, t: Target |
		add [b, b", n, t] and n != n"
		implies
		lookup [b, n"] = lookup [b", n"]
}

// This shows a counterexample similar to Fig 2.13
check addLocal for 3 but 2 Book

assert lookupYields {
	all b: Book, n: b.names | some lookup [b,n]
}

// This shows a counterexample similar to Fig 2.12
check lookupYields for 4 but 1 Book
