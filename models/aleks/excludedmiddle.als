-----------------------------------------
-- run with overflow prevention turned on
-----------------------------------------
-- no counterexample
check {
  4.plus[5] = 6.plus[3]
} for 4 Int 

-- no counterexample
check {
  4.plus[5] != 6.plus[3]
} for 4 Int 

-- no counterexample
check {
  all x: Int | x.mul[2] < 0 or !(x.mul[2] < 0)
} for 3 Int


one sig S { x: one Int }

-- returns only values which don't cause an overflow when multiplied by 2
run {
  S.x.mul[2] < 0 or !(S.x.mul[2] < 0)
} for 3 Int

