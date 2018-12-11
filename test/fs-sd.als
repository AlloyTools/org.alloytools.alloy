module chapter4/filesystem ----- The model from page 125

abstract sig Object {}

sig Dir extends Object {contents: set Object}

one sig Root extends Dir { }

sig File extends Object {}

fact {
	Object in Root.*contents
	}

assert SomeDir {
	all o: Object - Root | some contents.o
	}
check SomeDir // This assertion is valid

