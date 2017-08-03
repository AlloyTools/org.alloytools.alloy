module tests/test

sig A extends B { }
sig B extends A { }
run { } // should say there is cyclic inheritance!
