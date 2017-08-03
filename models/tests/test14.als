module tests/test // Bugpost by g.a.c.rijnders AT gmail.com

sig Foo {
  Foo: one Foo
}

run {} expect 1
