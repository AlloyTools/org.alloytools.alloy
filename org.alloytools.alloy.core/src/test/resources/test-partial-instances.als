sig B {}
sig A { r: lone B}
sig C { t: set Int}

inst exact_bound {
  0 Int,
  exactly 1 A,
  exactly 1 B,
  exactly 2 C
}

inst exact_named_bound {
  A = a1,
  B = b1,
  r = a1->b1,
  no C
}

inst lower_bound {
  A = a1 + a2,
  B = b1,
  r include a1->b1,
  no C
}

inst upper_bound {
  A in a1 + a2,
  B = b1,
  r include a1->b1,
  no C
}

inst range_bound {
  A in a1 + a2,
  B include b1 moreover b2,
  r include a1->b1,
  no C
}

inst continued_int_bound {
  2 Int,
  no A,
  no B,
  no C
}

inst sparse_int_bound {
  1 Int,
  no A,
  no B,
  C in c1,
  t = c1->10 + c1->11 + c1->12
}

inst default_bound {}

run {} for default_bound
