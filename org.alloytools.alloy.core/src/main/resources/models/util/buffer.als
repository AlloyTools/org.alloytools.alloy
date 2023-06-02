module util/buffer[BufIdx, elem]

open util/ordering[BufIdx] as ord

/** returns all the elements in this sequence */
fun elems [R: BufIdx->elem]: set elem { BufIdx.(R) }

/** returns the first element in the sequence */
fun firstElem [R: BufIdx->elem]: lone elem { ord/first.R }

/** returns the last element in the sequence */
fun lastElem [R: BufIdx->elem]: lone elem { R.at[R.lastIdx] }

/** true if the sequence is empty */
pred isEmpty [R: BufIdx -> elem] { no R}

/** returns last index occupied by this sequence */
fun lastIdx [R: BufIdx->elem] : lone BufIdx { ord/max[R.elem] }

/** returns all the indices occupied by this sequence */
fun inds [R: BufIdx->elem] : set BufIdx { elem.~(R) }

/** returns element at the given index */
fun at [R: BufIdx->elem, i: BufIdx]: lone elem { i.(R) }

/**
 * returns the index after the last index
 * if this sequence is empty, returns the first index,
 * if this sequence is full, returns empty set
 */
fun afterLastIdx [R: BufIdx->elem] : lone BufIdx {
  ord/min[BufIdx - R.inds]
}

/** true if this sequence has duplicates */
pred hasDups [R: BufIdx->elem] { # elems[R] < # inds[R] }

/** added is the result of appending e to the end of R */
pred add [R: BufIdx->elem, R_next: BufIdx->elem, e: elem] {
  R_next = R + (R.afterLastIdx -> e)
}

/** 
 * Set the first element in R_next
 * Copy over the remaning elements from R to R_next
*/
pred addFirst [R: BufIdx->elem, R_next: BufIdx->elem, e: elem] {
  R_next.firstElem = e 
  some R => { (all i: R.inds - firstIdx | R_next.at[i] = R.at[ord/prev[i]]) and R_next.at[R.afterLastIdx] = R.lastElem }
}

/** Substract the relation (lastIndex -> lastElem) from the set of relations in R */
pred remove [R: BufIdx->elem, R_next: BufIdx->elem] {
  R_next = R - (lastIdx[R] -> lastElem[R])
}

/** 
 * R_next[index - 1] = R[index] for each index > 0 in R. The first index is not copied since we are removing it
 * The lastIndex in R_next is equal to (lastIndex - 1) in R
*/
pred removeFirst [R: BufIdx->elem, R_next: BufIdx->elem] {
    one R.inds => (no R_next.inds) else {
	    (all i: R.inds - ord/first | R_next.at[ord/prev[i]] = R.at[i]) 
	    lastIdx[R_next] = ord/prev[lastIdx[R]]
    }
}

fun firstIdx: BufIdx { ord/first }
