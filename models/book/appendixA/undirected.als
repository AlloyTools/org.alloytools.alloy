module appendixA/undirected

sig Node { adjs: set Node }

pred acyclic {
	adjs = ~adjs
	// You have to fill in additional formula here
}

run acyclic for 4

