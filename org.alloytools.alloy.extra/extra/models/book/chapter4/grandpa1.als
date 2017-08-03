module language/grandpa1 ---- Page 84, 85

abstract sig Person {
	father: lone Man,
	mother: lone Woman
	}

sig Man extends Person {
	wife: lone Woman
	}

sig Woman extends Person {
	husband: lone Man
	}

fact {
	no p: Person | p in p.^(mother+father)
	wife = ~husband
	}

assert NoSelfFather {
	no m: Man | m = m.father
	}

// This should not find any counterexample.
check NoSelfFather

fun grandpas [p: Person] : set Person {
	p.(mother+father).father
	}

pred ownGrandpa [p: Person] {
	p in p.grandpas
	}

// This should not find any instance.
run ownGrandpa for 4 Person

assert NoSelfGrandpa {
	no p: Person | p in p.grandpas
	}

// This should not find any counterexample
check NoSelfGrandpa for 4 Person
