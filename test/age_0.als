
// unsat
one sig Person {
   age : one Age,
   children : one Person
}
sig Age in Int {}

fact{
   all p : Person | p.age > 0   
}

fact GTChildrenAge{
   all p : Person | all c : p.children| p.age > c.age
}
