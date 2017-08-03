module tests/test

open util/ordering[A] as ao
open util/ordering[B] as bo
open util/seqrel[ao/Ord] as ro
open r // this line should say "module r cannot be found"
