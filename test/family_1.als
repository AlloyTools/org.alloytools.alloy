abstract sig Person {
	spouse: lone Person,
	parents: set Person
}

sig Men, Women extends Person {}
one sig Adam extends Men {}
one sig Eve extends Women {}

fact Biological {

-- 2 parents: Man and Woman
all p : Person | lone p.parents & Women and lone p.parents & Men

-- No person can be  its ancestor
no p : Person | p in p.^parents
}

fact Social {
-- Symetric spouse
 spouse = ~spouse

-- a spouse cannot be a sibling
no p: Person | p.spouse in p.parents.~parents
}


fact Bible {
-- Adam and Eve married
  Eve in Adam.spouse

-- Adam and Eve have no parents
no (Adam + Eve).parents

-- Except Adam and Eve all others have a mother and a father
--    all p: Person - (Adam + Eve)| #p.parents = 2
} 


-- Without parenthesis the meaning of a => b and c => d is a => (b and c) => d
-- which can be understand as : if p is a men than if p is a woman and married to a woman then p.spouse is a man.
-- if p is a woman than the expression is true
-- if p is a man than, as p cannot be a woman, the expression is true
assert HeteroSexError {
all p : Person | p in Men => p.spouse in Women and p in Women => p.spouse in Men
}
check HeteroSexError for 30
