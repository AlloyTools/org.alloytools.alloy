abstract sig A {

} 

sig B extends A {
  f1 : C,
  f21 : H
}

sig C extends A {
  f2 : lone B
}

sig D in A {
  f  : C,
  f3 : B -> C,
  f4 : B -> lone C,  
  f5 : B -> one C,  
  f6 : B -> some C,      
  f7 : B one -> C,      
  f8 : B one -> lone C,    
  f9 : B one -> some C,      
  f10 : B lone -> C,      
  f11 : B lone -> lone C,    
  f12 : B lone -> some C,      
  f13 : B some -> C,      
  f14 : B some -> lone C,    
  f15 : B some -> some C,      
  f16 : B one -> C,      
  f17 : B one -> lone C,    
  f18 : B one -> some C           
}{
  f in A
}

sig H {
  f20 : J
}
sig J {}

fact {
  {a : H, b : J | a.f1 = b} in f1
}

sig E in B + C {
  f19 : some D
}

sig F {}

sig K {}

sig P {}
sig Q {}

sig G in Int {}



fact fact6 {
  f19.D in B
  all e : E | e.^f19 in B
  all e1 : E | some e2 : D | disj[e1, e2]
  B + C - E in A
  (D <: f1) in (A -> C)
}

fact fact7 {
  f19 in *f19
  (D -> C) in (f1 ++ f & (D -> C))
}

fact fact8 {
  -1 =< #(B)  
  #(A) < 3
  4 >= #(B)
  #(E.f19) =< 9
  #(f) =< 4
}

fact fact9 {
  {b : B | b.f1 in (C + B)} in A
}



