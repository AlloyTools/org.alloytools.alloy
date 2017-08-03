module language/grandpa3 ---- the final model in fig 4.4

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

fact Biology {
	no p: Person | p in p.^(mother+father)
	}

fact Terminology {
	wife = ~husband
	}

fact SocialConvention {
	no (wife+husband) & ^(mother+father)
	}

------------------------------------------

assert NoSelfFather {
	no m: Man | m = m.father
	}

// This should not find any counterexample.
check NoSelfFather

------------------------------------------

fun grandpas [p: Person] : set Person {
	let parent = mother + father + father.wife + mother.husband |
		p.parent.parent & Man
	}

pred ownGrandpa [p: Person] {
	p in p.grandpas
	}

// This generates an instance similar to Fig 4.3
run ownGrandpa for 4 Person

------------------------------------------

pred SocialConvention1 {
	no (wife + husband) & ^(mother + father)
	}

pred SocialConvention2 {
	let parent = mother + father {
		no m: Man | some m.wife and m.wife in m.*parent.mother
		no w: Woman | some w.husband and w.husband in w.*parent.father
		}
	}

// This assertion was described on page 90.
assert Same {
	SocialConvention1 iff SocialConvention2
	}

// This should not find any counterexample
check Same
