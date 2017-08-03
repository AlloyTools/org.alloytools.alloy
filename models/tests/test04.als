module tests/test

open util/ordering[Int] as ord

sig A {}

one sig A1,A2,A3 extends A {}

run {} for 0 expect 1
run {} for 1 expect 1
run {} for 2 expect 1
run {} for 3 expect 1
run {} for 4 expect 1
