module appendixA/closure

pred transCover [R, r: univ->univ] {
	// You have to fill in the appropriate formula here
}

pred transClosure [R, r: univ->univ] {
	transCover [R, r]
	// You have to fill in the appropriate formula here
}

assert Equivalence {
	all R, r: univ->univ | transClosure [R,r] iff R = ^r
}

check Equivalence for 3
