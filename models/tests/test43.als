module tests/test

sig A { x,y:Int } { no x & y  }
sig B { x,y:Int } { }
run { some b:B | some b.x } expect 1
run { some a:A | some a.x } expect 1
run { some a:A | some (a.x & a.y) } expect 0
