
enum Bool { true, false}
sig Foo {
	bar : Bool
}

run { all f : Foo | f.bar and (Foo-f).bar } 


