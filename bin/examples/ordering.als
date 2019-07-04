open util/ordering[A] as ordA
sig A {}
one sig A0, A1, A2 extends A{}
fact {nexts [A0] = A1 + A2}
