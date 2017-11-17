sig Foo { n : lone Foo }
pred a[ f : Foo ] { some f.n implies b[f.n] }
pred b[ f : Foo ] { some f.n implies a[f.n] }

run a for 4