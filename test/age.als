// sat
sig Person {
   age : one Age
}
sig Age in Int {}

fact{
   all p : Person | p.age > 0
}
