module appendixA/distribution

assert union {
	all s: set univ, p, q: univ->univ | s.(p+q) = s.p + s.q
}

check union for 4
