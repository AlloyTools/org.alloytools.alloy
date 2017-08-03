pred p[a, b: Int] {
  a.plus[b] > a
}

pred q[a, b: Int] {
  a.plus[b] > b
}

check {
  all a, b: Int | (p[a,b] => q[a,b]) iff (not q[a, b]) => (not p[a, b])
} for 4 Int
