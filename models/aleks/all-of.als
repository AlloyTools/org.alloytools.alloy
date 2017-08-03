check {
  all x: Int | x != 0 => x.div[x] = 1 else x > 0
} for 3 Int
