module util/relation

/*
 * Utilities for some common operations and constraints
 * on binary relations. The keyword 'univ' represents the
 * top-level type, which all other types implicitly extend.
 * Therefore, all the functions and predicates in this model
 * may be applied to binary relations of any type.
 *
 * author: Greg Dennis
 */

/** returns the domain of a binary relation */
fun dom [r: univ->univ] : set (r.univ) { r.univ }

/** returns the range of a binary relation */
fun ran [r: univ->univ] : set (univ.r) { univ.r }

/** r is total over the domain s */
pred total [r: univ->univ, s: set univ] {
  all x: s | some x.r
}

/** r is a partial function over the domain s */
pred functional [r: univ->univ, s: set univ] {
  all x: s | lone x.r
}

/** r is a total function over the domain s */
pred function [r: univ->univ, s: set univ] {
  all x: s | one x.r
}

/** r is surjective over the codomain s */
pred surjective [r: univ->univ, s: set univ] {
  all x: s | some r.x
}

/** r is injective */
pred injective [r: univ->univ, s: set univ] {
  all x: s | lone r.x
}

/** r is bijective over the codomain s */
pred bijective[r: univ->univ, s: set univ] {
  all x: s | one r.x
}

/** r is a bijection over the domain d and the codomain c */
pred bijection[r: univ->univ, d, c: set univ] {
  function[r, d] && bijective[r, c]
}

/** r is reflexive over the set s */
pred reflexive [r: univ -> univ, s: set univ] {s<:iden in r}

/** r is irreflexive */
pred irreflexive [r: univ -> univ] {no iden & r}

/** r is symmetric */
pred symmetric [r: univ -> univ] {~r in r}

/** r is anti-symmetric */
pred antisymmetric [r: univ -> univ] {~r & r in iden}

/** r is transitive */
pred transitive [r: univ -> univ] {r.r in r}

/** r is acyclic over the set s */
pred acyclic[r: univ->univ, s: set univ] {
  all x: s | x !in x.^r
}

/** r is complete over the set s */
pred complete[r: univ->univ, s: univ] {
  all x,y:s | (x!=y => x->y in (r + ~r))
}

/** r is a preorder (or a quasi-order) over the set s */
pred preorder [r: univ -> univ, s: set univ] {
  reflexive[r, s]
  transitive[r]
}

/** r is an equivalence relation over the set s */
pred equivalence [r: univ->univ, s: set univ] {
  preorder[r, s]
  symmetric[r]
}

/** r is a partial order over the set s */
pred partialOrder [r: univ -> univ, s: set univ] {
  preorder[r, s]
  antisymmetric[r]
}

/** r is a total order over the set s */
pred totalOrder [r: univ -> univ, s: set univ] {
  partialOrder[r, s]
  complete[r, s]
}
