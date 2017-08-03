module tests/test48a[x]

sig y extends x { g: set f } // This should give a "f cannot be found" error
