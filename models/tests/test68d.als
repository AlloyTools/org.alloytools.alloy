module tests/test

open tests/test68b
open tests/test68a

sig C extends A1 {}
run { some C } expect 1
