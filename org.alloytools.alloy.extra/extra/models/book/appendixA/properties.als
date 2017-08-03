module appendixA/properties

pred show {
	some r: univ->univ {
		some r			-- nonempty
		r.r in r			-- transitive
		no iden & r		-- irreflexive
		~r in r			-- symmetric
		~r.r in iden		-- functional
		r.~r in iden		-- injective
		univ in r.univ	-- total
		univ in univ.r	-- onto
		}
	}

run show for 4

assert ReformulateNonEmptinessOK {
	all r: univ->univ |
		some r iff (some x, y: univ | x->y in r)
	}

check ReformulateNonEmptinessOK
