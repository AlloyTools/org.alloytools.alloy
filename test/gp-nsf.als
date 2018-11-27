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

