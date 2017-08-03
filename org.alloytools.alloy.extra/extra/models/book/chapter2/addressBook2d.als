module tour/addressBook2d ----- Page 21

abstract sig Target { }
sig Addr extends Target { }
abstract sig Name extends Target { }

sig Alias, Group extends Name { }

sig Book {
	addr: Name->Target
} {
	no n: Name | n in n.^addr
	all a: Alias | lone a.addr
}

pred show [b:Book]   { some Alias.(b.addr) }

// This command generates an instance similar to Fig 2.12
run show for 3 but 1 Book
