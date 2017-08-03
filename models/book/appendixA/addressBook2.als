module appendixA/addressBook2

sig Addr, Name { }

sig Book {
	addr: Name -> (Name + Addr)
	}

pred inv [b: Book] {
	let addr = b.addr |
		all n: Name {
			n not in n.^addr
			some addr.n => some n.^addr & Addr
		}
	}

pred add [b, b': Book, n: Name, t: Name+Addr] {
	b'.addr = b.addr + n->t
	}

pred del [b, b': Book, n: Name, t: Name+Addr] {
	b'.addr = b.addr - n->t
	}

fun lookup [b: Book, n: Name] : set Addr {
	n.^(b.addr) & Addr
	}
