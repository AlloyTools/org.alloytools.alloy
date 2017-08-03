module tour/addressBook1h ------- Page 14..16

sig Name, Addr { }

sig Book {
	addr: Name -> lone Addr
}

pred show [b: Book] {
	#b.addr > 1
	#Name.(b.addr) > 1
}
run show for 3 but 1 Book

pred add [b, b': Book, n: Name, a: Addr] {
	b'.addr = b.addr + n->a
}

pred del [b, b': Book, n: Name] {
	b'.addr = b.addr - n->Addr
}

fun lookup [b: Book, n: Name] : set Addr {
	n.(b.addr)
}

pred showAdd [b, b': Book, n: Name, a: Addr] {
	add [b, b', n, a]
	#Name.(b'.addr) > 1
}
run showAdd for 3 but 2 Book

assert delUndoesAdd {
	all b, b', b'': Book, n: Name, a: Addr |
		no n.(b.addr) and add [b, b', n, a] and del [b', b'', n]
		implies
		b.addr = b''.addr
}

assert addIdempotent {
	all b, b', b'': Book, n: Name, a: Addr |
		add [b, b', n, a] and add [b', b'', n, a]
		implies
		b'.addr = b''.addr
}

assert addLocal {
	all b, b': Book, n, n': Name, a: Addr |
		add [b, b', n, a] and n != n'
		implies
		lookup [b, n'] = lookup [b', n']
}

// This command should not find any counterexample.
check delUndoesAdd for 3

// This command should not find any counterexample.
check delUndoesAdd for 10 but 3 Book

// This command should not find any counterexample.
check addIdempotent for 3

// This command should not find any counterexample.
check addLocal for 3 but 2 Book
