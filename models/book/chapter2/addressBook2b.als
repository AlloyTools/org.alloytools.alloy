module tour/addressBook2b ----- Page 19

abstract sig Target { }
sig Addr extends Target { }
abstract sig Name extends Target { }

sig Alias, Group extends Name { }

sig Book {
	addr: Name->Target
} {
	no n: Name | n in n.^addr
}

pred show [b:Book]   { some b.addr }

// This command generates an instance similar to Fig 2.10
run show for 3 but 1 Book
