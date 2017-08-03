module tests/test

open util/relation
open util/relation as a
run a/acyclic expect 1
run relation/acyclic expect 1
