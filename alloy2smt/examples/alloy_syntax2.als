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

fact setcomp{
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

fact fact1 {
  all b : B | b.f1 in C
  lone b : B | b.f1 in C
  no c : C | c.f2 in D
  some b : B | b.f1 in C
}

fact fact2 {
  all b : B, c : C | (b -> c) in (B -> C)
  all b : B | no f : F | f in b.f1
  all b : B | lone h : H | h in b.f21
  all b : B | some h : H | h !in b.f21  
}

fact fact3 {
  some c : C | all u : univ | univ & none = none
  some c : C | some u : univ | univ - none = univ  
  some c : C | lone k : K |  k in univ
  some c : C | no k : K |  (c -> k) in f1  
}

fact fact4 {
  lone p : P | all q : Q | p & q = none
  no p : P | some q : Q | p -> q in f1
}
