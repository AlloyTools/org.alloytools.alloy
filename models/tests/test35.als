module tests/test

abstract sig A {f:set univ}

one sig A1,A2,A3 extends A {}

run { f=A1->A2 && f in A->one A } expect 0
run { f=A1->A2 && f in A->some A } expect 0
run { f=A1->A2 && f in A->lone A } expect 1
run { f=A1->A2 && f in A->set A } expect 1
