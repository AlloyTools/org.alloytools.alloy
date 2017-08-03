module tour/addressBook2a ----- Page 18

abstract sig Target { }
sig Addr extends Target { }
abstract sig Name extends Target { }

sig Alias, Group extends Name { }

sig Book {
	addr: Name->Target
}

pred show [b:Book]   { some b.addr }

// This command generates an instance similar to Fig 2.9
run show for 3 but 1 Book
