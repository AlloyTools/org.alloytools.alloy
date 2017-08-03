module tests/test

open util/ordering[A] as ord

sig A {}

one sig A1,A2,A3 extends A {}

run { first=A1 } for 3 expect 1
run { first=A2 } for 3 expect 1
run { first=A3 } for 3 expect 1
run { first!=A1 && first!=A2 && first!=A3 } for 3 expect 0
run { first!=A1 && first!=A2 && first!=A3 } for 4 expect 1

