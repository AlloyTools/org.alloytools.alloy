module tests/test // Bugpost by C. M. Sperberg-McQueen <cmsmcq@acm.org>

sig Name {}
one sig Document, Schema extends Name {}

pred test1 (d: Document,  s: Schema) { disj[d, s] }
run test1 expect 1

pred test2 (n1, n2: Name) { disj[n1, n2] }
run test2 expect 1

pred test3 (d1, d2: Document) { disj[d1, d2] }
run test3 expect 0

pred test4 (d: Document,  s: Name) { disj[d, s] }
run test4 expect 1
