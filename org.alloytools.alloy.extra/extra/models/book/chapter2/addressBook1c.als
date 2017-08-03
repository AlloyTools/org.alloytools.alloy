module tour/addressBook1c ----- Page 8

sig Name, Addr { }

sig Book {
	addr: Name -> lone Addr
}

pred show [b: Book] {
	#b.addr > 1
	some n: Name | #n.(b.addr) > 1
}

// This command should not find any instance.
run show for 3 but 1 Book
