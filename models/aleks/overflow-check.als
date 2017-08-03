open util/integer 

/* ~~~~~~~~~ addition ~~~~~~~~~ */

sig S_add {
  a, b, res: one Int
} {
  res = add[a, b]
}

check plus_doesnt_overflow {
  all s: S_add | 
    (s.a > 0 and s.b > 0 => s.res > 0) and
    (s.a < 0 and s.b < 0 => s.res < 0)
} for 0 but 4 Int, exactly 1 S_add

/* ~~~~~~~~~ subtraction ~~~~~~~~~ */

sig S_sub {
  a, b, res: one Int
} {
  res = sub[a, b]
}

check minus_doesnt_overflow {
  all s: S_sub |
    (s.a > 0 and s.b < 0 => s.res > 0) and
    (s.a < 0 and s.b > 0 => s.res < 0)
} for 0 but 5 Int, exactly 1 S_sub

/* ~~~~~~~~~ multiplication ~~~~~~~~~ */

sig S_mul {
  a, b, res: one Int
} {
  res = mul[a, b]
}

check mul_doesnt_overflow {
  all s: S_mul |
    (s.a > 0 and s.b > 0 => s.res > 0) and
    (s.a < 0 and s.b < 0 => s.res > 0) and
    (s.a > 0 and s.b < 0 => s.res < 0) and
    (s.a < 0 and s.b > 0 => s.res < 0)
} for 0 but 5 Int, exactly 1 S_mul

check mul_ok_1 {
  all s: S_mul | 
    mul[s.a, s.b] = mul[s.a, s.b] and
    s.a = 0 or s.b = 0 implies s.res = 0   and
    s.a = 1            implies s.res = s.b and
    s.b = 1            implies s.res = s.a and
    s.a = -1           implies s.res = sub[0, s.b] and
    s.b = -1           implies s.res = sub[0, s.a]
} for 0 but 5 Int, exactly 1 S_mul

check mul_ok_2 {
  all x, y: Int |
    ((x = 2   and y >= 4)  or 
     (x >= 3  and y >= 3)  or 
     (x = -2  and y <= -5) or
     (x <= -3 and y <= -3)) 
    implies
      -- "not (some mul[x, y])" wouldn't work because 
      -- e.g. mul[4, 5] doesn't evaluate to an empty set, rather, it doesn't exist
     (no s: S_mul | s.a = x and s.b = y)
} for 0 but 4 Int, exactly 1 S_mul

/* ~~~~~~~~~ division ~~~~~~~~~ */

sig S_div {
  a, b, res: one Int
} {
  res = div[a, b]
}

/* ~~~~~~~~ shift left ~~~~~~~~ */

sig S_shl {
  a, b, res: one Int
} {
  res = a << b
}

check shl_doesnt_overflow {
  all s: S_shl | 
    (s.a > 0 and s.b > 0 => s.res > 0) and
    (s.a < 0 and s.b > 0 => s.res < 0)
} for 0 but 5 Int, exactly 1 S_shl

check shl_overflows_for_neg {
  no s: S_shl | s.a != 0 and s.b < 0
} for 0 but 5 Int, exactly 1 S_shl


