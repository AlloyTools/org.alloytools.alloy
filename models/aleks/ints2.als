sig R {}

one sig S {
  a, b, c : set R
}

run {
  S.a + S.b = S.c
} for 2
