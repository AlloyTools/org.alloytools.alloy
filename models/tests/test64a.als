module tests/test

open tests/test64b as b
open tests/test64c as c
let mac=4
run { this/mac=4   b/mac=5  c/mac=6 } expect 1
