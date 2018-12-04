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
   all p: Person - (Adam + Eve)| #p.parents = 2
} 

assert HeteroSexError {
all p : Person | p in Men => p.spouse in Women and p in Women => p.spouse in Men
}
assert  NoSelfMarriage {
  -- You can't marry yourself
 no p : Person | p in p.spouse
}
check NoSelfMarriage for 30
check HeteroSexError for 30
