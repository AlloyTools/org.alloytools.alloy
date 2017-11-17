module util/integer

/*
 * A collection of utility functions for using Integers in Alloy.
 * Note that integer overflows are silently truncated to the current bitwidth
 * using the 2's complement arithmetic, unless the "forbid overfows" option is
 * turned on, in which case only models that don't have any overflows are 
 * analyzed. 
 */

fun add  [n1, n2: Int] : Int { this/plus[n1, n2] }
fun plus [n1, n2: Int] : Int { n1 fun/add n2 }

fun sub   [n1, n2: Int] : Int { this/minus[n1, n2] }
fun minus [n1, n2: Int] : Int { n1 fun/sub n2 }

fun mul [n1, n2: Int] : Int { n1 fun/mul n2 }

/**
 * Performs the division with "round to zero" semantics, except the following 3 cases
 * 1) if a is 0, then it returns 0
 * 2) else if b is 0, then it returns 1 if a is negative and -1 if a is positive
 * 3) else if a is the smallest negative integer, and b is -1, then it returns a
 */
fun div [n1, n2: Int] : Int { n1 fun/div n2 }

/** answer is defined to be the unique integer that satisfies "a = ((a/b)*b) + remainder" */
fun rem [n1, n2: Int] : Int { n1 fun/rem n2 }

/** negate */
fun negate [n: Int] : Int { 0 fun/sub n }

/** equal to */
pred eq [n1, n2: Int] { int[n1] = int[n2] }

/** greater than */
pred gt [n1, n2: Int] { n1 > n2 }

/** less then */
pred lt [n1, n2: Int] { n1 < n2 }

/** greater than or equal */
pred gte [n1, n2: Int] { n1 >= n2 }

/** less than or equal */
pred lte [n1, n2: Int] { n1 <= n2 }

/** integer is zero */
pred zero [n: Int] { n = 0 }

/** positive */
pred pos  [n: Int] { n > 0 }

/** negative */
pred neg  [n: Int] { n < 0 }

/** non-positive */
pred nonpos [n: Int] { n <= 0 }

/** non-negative */
pred nonneg [n: Int] { n >= 0 }

/** signum (aka sign or sgn) */
fun signum [n: Int] : Int { n<0 => (0 fun/sub 1) else (n>0 => 1 else 0) }

/**
 * returns the ith element (zero-based) from the set s
 * in the ordering of 'next', which is a linear ordering
 * relation like that provided by util/ordering
 */
fun int2elem[i: Int, next: univ->univ, s: set univ] : lone s {
  {e: s | #^next.e = int i }
}

/**
 * returns the index of the element (zero-based) in the
 * ordering of next, which is a linear ordering relation
 * like that provided by util/ordering
 */
fun elem2int[e: univ, next: univ->univ] : lone Int {
  Int[#^next.e]
}

/** returns the largest integer in the current bitwidth */
fun max:one Int { fun/max }

/** returns the smallest integer in the current bitwidth */
fun min:one Int { fun/min }

/** maps each integer (except max) to the integer after it */
fun next:Int->Int { fun/next }

/** maps each integer (except min) to the integer before it */
fun prev:Int->Int { ~next }

/** given a set of integers, return the largest element */
fun max [es: set Int]: lone Int { es - es.^prev }

/** given a set of integers, return the smallest element */
fun min [es: set Int]: lone Int { es - es.^next }

/** given an integer, return all integers prior to it */
fun prevs [e: Int]: set Int { e.^prev }

/** given an integer, return all integers following it */
fun nexts [e: Int]: set Int { e.^next }

/** returns the larger of the two integers */
fun larger [e1, e2: Int]: Int { let a=int[e1], b=int[e2] | (a<b => b else a) }

/** returns the smaller of the two integers */
fun smaller [e1, e2: Int]: Int { let a=int[e1], b=int[e2] | (a<b => a else b) }
