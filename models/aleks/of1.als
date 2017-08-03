sig A { 
  relA: set A, 
  relB: set A 
}

fact cont {
	relA in relB
}

fact g {
	#(relA) > #(relB)
}

run {  } for 3 int
