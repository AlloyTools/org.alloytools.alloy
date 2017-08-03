module tour/addressBook1d ----- Page 9

sig Name, Addr { }

sig Book {
	addr: Name -> lone Addr
}

pred show [b: Book] {
	#b.addr > 1
	#Name.(b.addr) > 1
}

// This command generates an instance similar to Fig 2.3
run show for 3 but 1 Book
