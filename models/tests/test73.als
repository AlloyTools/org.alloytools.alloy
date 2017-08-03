module tests/test

one sig A { }
fun B : univ { sig$ }
run { } for 7 expect 1
