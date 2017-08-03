module tests/test // Bugpost by Jan van Eijck (Jan.van.Eijck AT cwi.nl)

sig Object { b: set Object }

one sig Root, A, B, C, D extends Object {}

fact OneRoot { all x: Object | x = Root <=> no b.x }

fact SingleParent
  { all x,y,z: Object | z in x.b and z in y.b => x=y }

fact b_acyclic { no ^b & iden }

fact { C in B.b and D in C.b }

pred show () {}

run show for 5 expect 1
