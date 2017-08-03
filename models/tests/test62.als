module tests/test // example contributed by Juan Pablo Galeotti

one sig L0 { H0: NULL+N }

sig N { N0: NULL+N }

one sig NULL {}

check { L0.H0.N0.N0.N0.N0.N0.N0.N0.N0.N0.N0.N0.N0.N0.N0.N0.N0.N0.N0.N0.N0.N0=NULL } for 20 expect 1
