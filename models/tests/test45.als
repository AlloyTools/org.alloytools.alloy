module tests/test --- example motivated by ikarus1983de@yahoo.de

abstract sig A { }
run { one A } for 3 but exactly 0 A expect 0
run { one A } for 3 but exactly 1 A expect 1
run { one A } for 3 but exactly 2 A expect 0
run { one A } for 3 but exactly 3 A expect 0

abstract sig B { }
sig B1 extends B { }
run { one B } for 3 but exactly 0 B expect 0
run { one B } for 3 but exactly 1 B expect 1
run { one B } for 3 but exactly 2 B expect 0
run { one B } for 3 but exactly 3 B expect 0

abstract sig C { }
sig C1,C2 extends C { }
run { one C } for 3 but exactly 0 C expect 0
run { one C } for 3 but exactly 1 C expect 1
run { one C } for 3 but exactly 2 C expect 0
run { one C } for 3 but exactly 3 C expect 0
