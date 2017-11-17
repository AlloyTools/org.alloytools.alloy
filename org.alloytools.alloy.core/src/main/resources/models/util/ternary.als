module util/ternary

/*
 * Utilities for some common operations and constraints
 * on ternary relations. The keyword 'univ' represents the
 * top-level type, which all other types implicitly extend.
 * Therefore, all the functions and predicates in this model
 * may be applied to ternary relations of any type.
 *
 * author: Greg Dennis
 */

/** returns the domain of a ternary relation */
fun dom [r: univ->univ->univ] : set ((r.univ).univ) { (r.univ).univ }

/** returns the range of a ternary relation */
fun ran [r: univ->univ->univ] : set (univ.(univ.r)) { univ.(univ.r) }

/** returns the "middle range" of a ternary relation */
fun mid [r: univ->univ->univ] : set (univ.(r.univ)) { univ.(r.univ) }

/** returns the first two columns of a ternary relation */
fun select12 [r: univ->univ->univ] : r.univ {
  r.univ
}

/** returns the first and last columns of a ternary relation */
fun select13 [r: univ->univ->univ] : ((r.univ).univ) -> (univ.(univ.r)) {
  {x: (r.univ).univ, z: univ.(univ.r) | some (x.r).z}
}

/** returns the last two columns of a ternary relation */
fun select23 [r: univ->univ->univ] : univ.r {
  univ.r
}

/** flips the first two columns of a ternary relation */
fun flip12 [r: univ->univ->univ] : (univ.(r.univ))->((r.univ).univ)->(univ.(univ.r)) {
  {x: univ.(r.univ), y: (r.univ).univ, z: univ.(univ.r) | y->x->z in r}
}

/** flips the first and last columns of a ternary relation */
fun flip13 [r: univ->univ->univ] : (univ.(univ.r))->(univ.(r.univ))->((r.univ).univ) {
  {x: univ.(univ.r), y: univ.(r.univ), z: (r.univ).univ | z->y->x in r}
}

/** flips the last two columns of a ternary relation */
fun flip23 [r: univ->univ->univ] : ((r.univ).univ)->(univ.(univ.r))->(univ.(r.univ)) {
  {x: (r.univ).univ, y: univ.(univ.r), z: univ.(r.univ) | x->z->y in r}
}
