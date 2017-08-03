open util/integer

one sig S {
  a : one Int, 
  b : one Int
}{
  a >= 0 and b >=0
}

run {
  add[S.a, S.b] = 2
} for 1
