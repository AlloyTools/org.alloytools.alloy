module tests/test

sig B extends A1 {}
abstract sig A {}
abstract sig A1 extends A {}
abstract sig A2 extends A {}
sig C extends A1 {}

run { some B } expect 1
