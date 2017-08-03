module tests/test // Bugpost by Emina Torlak

open util/sequence[A] as aseq
open util/sequence[B] as bseq

sig A {}
sig B {}

fact  {
  // This line works
  all a: A | some (Seq.seqElems).a
  // This line should work, but typechecker had a bug, and find Seq ambiguous
  all a: A | some indsOf[Seq,a]
}

run {} expect 1
