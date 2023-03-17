/*
	Src: Bounded Model Checking of Temporal Formulas with Alloy by Alcino Cunha
	Modified to change s' to s_next for Alloy 6
*/
module util/traces[exactly elem]

private one sig Ord {
   First: set elem,
   Next: elem -> elem
} {
   pred/totalOrder[elem,First,Next]
}

lone sig back in elem {}

fun loop : elem -> elem {
	last -> back
}

fun first: one elem { Ord.First }

fun last: one elem { elem - ((Ord.Next).elem) }

fun next : elem->elem { Ord.Next + loop }

fun prev : elem->elem { ~this/next }

fun past : elem->elem { ^(~this/next) }

fun future : elem -> elem { elem <: *this/next }

fun upto[s,s_next : elem] : set elem {
	(s_next in s.*(Ord.Next) or finite) implies s.future & ^(Ord.Next).s_next else s.*(Ord.Next) + (^(Ord.Next).s_next & back.*(Ord.Next))
}


pred finite {
	no loop
}

pred infinite {
	some loop
}

check total {
	finite implies pred/totalOrder[elem,first,next]
}
