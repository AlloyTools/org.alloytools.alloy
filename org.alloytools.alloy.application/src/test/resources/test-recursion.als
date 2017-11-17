sig Foo { n : lone Foo }
pred t[ f : Foo ] { some f.n implies t[f.n] }

run t for 4