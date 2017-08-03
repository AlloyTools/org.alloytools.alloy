one sig S {
  a : set Int, 
  b : set Int
}

run {
  S.a - S.b = 5 + 2 and #(S.a & S.b)=2
} for 1
