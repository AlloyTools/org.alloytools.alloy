module tests/test

open util/ordering[Int] as ord
open util/integer as ui

run { first=Int[0-2-2] } for 3 int expect 1
run { first=Int[0-3] } for 3 int expect 1
run { first=Int[0-2] } for 3 int expect 1
run { first=Int[0-1] } for 3 int expect 1
run { first=Int[0]   } for 3 int expect 1
run { first=Int[1]   } for 3 int expect 1
run { first=Int[2]   } for 3 int expect 1
run { first=Int[3]   } for 3 int expect 1
run { first=ui/max } expect 1
run { first=ui/min } expect 1
run { first->last in ui/next } expect 1
run { some 2.mul[3] } expect 1
run { some 5.div[3] } expect 1
run { some 5.rem[3] } expect 1
