sig A, B, C in Int {}
 fact {
     A = 1 + 2
     B = 4 + 5
     C = plus[A, B]
 }
run {} for 5 Int, 12 seq
