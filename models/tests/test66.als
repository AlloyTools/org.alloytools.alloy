module tests/test

pred p[t: univ] {
  all t' : univ - t | #{v: univ | t' in t} > 0
}

run {no x: univ | p[x] } for 1 expect 1
