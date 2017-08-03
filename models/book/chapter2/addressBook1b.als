module tour/addressBook1b ----- Page 8

sig Name, Addr { }

sig Book {
	addr: Name -> lone Addr
}

pred show [b: Book] {
	#b.addr > 1
}

// This command generates an instance similar to Fig 2.2
run show for 3 but 1 Book
