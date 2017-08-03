module tests/test

sig A { f: A }

sig B { f: B }

sig C in A+B { g: f } // Should give an ambiguity error
