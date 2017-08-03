module tests/test54c

open tests/test54b as b

sig Y extends X { g: f } // This line SHOULD SUCCEED

run {} expect 1
