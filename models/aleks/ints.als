open util/integer

one sig S {
  a: one Int, 
  b: one Int,
  c: one Int
} { 
  b != 0 => c = div[a, b] else c = a
}

run {
  S.b = 0
} for 3 Int
