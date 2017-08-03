module tests/test

sig A { }
sig B extends A { }
run { some B$ } for 2 A expect 1
