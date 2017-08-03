module appendixA/spanning

pred isTree [r: univ->univ] {
	// You have to fill in the appropriate formula here
}

pred spans [r1, r2: univ->univ] {
	// You have to fill in the appropriate formula here
}

pred show [r, t1, t2: univ->univ] {
	spans [t1,r] and isTree [t1]
	spans [t2,r] and isTree [t2]
	t1 != t2
}

run show for 3
