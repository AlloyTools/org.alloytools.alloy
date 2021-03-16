module util/natural

/*
 * Utility function and predicates for using the set of
 * nonnegative integers (0, 1, 2, . . .). The number of
 * naturals present in an analysis will be equal to the
 * scope on Natural. Specifically, if the scope on Natural
 * is N, then the naturals 0 through N-1 will be present.
 *
 * Note that the functions that return Naturals, such as
 * 'add' and 'div', may return an empty set if no such
 * Natural exists for that integer value.
 *
 * To write an Alloy model that makes use of negative
 * integers, use the util/integer module instead.
 *
 * @author Greg Dennis
 */

private open util/ordering[Natural] as ord
private open util/integer as integer

sig Natural {}

/** the integer zero */
one sig Zero in Natural {}

/** the integer one will be the empty set if the scope on Natural is less than two */
lone sig One in Natural {}

fact {
  first in Zero
  next[first] in One
}

/** returns n + 1 */
fun inc [n: Natural] : lone Natural { ord/next[n] }

/** returns n - 1 */
fun dec [n: Natural] : lone Natural { ord/prev[n] }

/** returns n1 + n2 */
fun add [n1, n2: Natural] : lone Natural {
  {n: Natural | #ord/prevs[n] = plus[#ord/prevs[n1], #ord/prevs[n2]]}
}

/** returns n1 - n2 */
fun sub [n1, n2: Natural] : lone Natural {
  {n: Natural | #ord/prevs[n1] = plus[#ord/prevs[n2], #ord/prevs[n]]}
}

/** returns n1 * n2 */
fun mul [n1, n2: Natural] : lone Natural {
  {n: Natural | #ord/prevs[n] = #(ord/prevs[n1]->ord/prevs[n2])}
}

/** returns n1 / n2 */
fun div [n1, n2: Natural] : lone Natural {
  {n: Natural | #ord/prevs[n1] = #(ord/prevs[n2]->ord/prevs[n])}
}

/**  returns true iff n1 is greater than n2 */
pred gt  [n1, n2: Natural] { ord/gt [n1, n2] }

/**  returns true iff n1 is less than n2 */
pred lt  [n1, n2: Natural] { ord/lt [n1, n2] }

/**  returns true iff n1 is greater than or equal to n2 */
pred gte [n1, n2: Natural] { ord/gte[n1, n2] }

/**  returns true iff n1 is less than or equal to n2 */
pred lte [n1, n2: Natural] { ord/lte[n1, n2] }

/** returns the maximum integer in ns */
fun max [ns: set Natural] : lone Natural { ord/max[ns] }

/** returns the minimum integer in ns */
fun min [ns: set Natural] : lone Natural { ord/min[ns] }
