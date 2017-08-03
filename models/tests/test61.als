module tests/test

open util/ordering[A] as ao
open util/ordering[B] as bo
open util/seqrel[A] as ro
sig A, B {}
run {C.next} // this line should complain about "C not found", and should complain only once (rather than 4 times!)
