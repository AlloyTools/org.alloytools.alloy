module tests/test

sig Foo {
  Foo: one Foo
  }

run { some univ } expect 1

