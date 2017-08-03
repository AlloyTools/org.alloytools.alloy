module tests/test

open tests/test68a
open tests/test68b

sig C extends A1 {}
run { some C } expect 1
