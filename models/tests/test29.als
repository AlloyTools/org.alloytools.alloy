module tests/test

sig A { x:Int, y:Int }
sig B { x:Int, z:Int }
sig C in A+B {}

run {} expect 1
