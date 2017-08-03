module tour/addressBook1a ----- Page 6

sig Name, Addr { }

sig Book {
	addr: Name -> lone Addr
}

pred show { }

// This command generates an instance similar to Fig 2.1
run show for 3 but 1 Book
