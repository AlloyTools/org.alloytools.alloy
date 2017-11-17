module util/sequniv

open util/integer as ui

/*
 * NOTE: Do not include this module manually.
 * Instead, use the "seq" keyword which will automatically
 * import this module with the correct additional constraints as needed.
 */

/*
 * A sequence utility for modeling sequences as just a
 * relation as opposed to reifying them into sequence
 * atoms like the util/sequence module does.
 *
 * Precondition: each input sequence must range over a prefix
 * of seq/Int.
 *
 * Postcondition: we guarantee the returned sequence
 * also ranges over a prefix of seq/Int.
 *
 * @author Greg Dennis
 */

/** sequence covers a prefix of seq/Int */
pred isSeq[s: Int -> univ] {
  s in seq/Int -> lone univ
  s.inds - ui/next[s.inds] in 0
}

/** returns all the elements in this sequence */
fun elems [s: Int -> univ]: set (Int.s) { seq/Int . s }

/**
 * returns the first element in the sequence
 * (Returns the empty set if the sequence is empty)
 */
fun first [s: Int -> univ]: lone (Int.s) { s[0] }

/**
 * returns the last element in the sequence
 * (Returns the empty set if the sequence is empty)
 */
fun last [s: Int -> univ]: lone (Int.s) { s[lastIdx[s]] }

/**
 * returns the cdr of the sequence
 * (Returns the empty sequence if the sequence has 1 or fewer element)
 */
fun rest [s: Int -> univ] : s { seq/Int <: ((ui/next).s) }

/** returns all but the last element of the sequence */
fun butlast [s: Int -> univ] : s {
  (seq/Int - lastIdx[s]) <: s
}

/** true if the sequence is empty */
pred isEmpty [s: Int -> univ] { no s }

/** true if this sequence has duplicates */
pred hasDups [s: Int -> univ] { # elems[s] < # inds[s] }

/** returns all the indices occupied by this sequence */
fun inds [s: Int -> univ]: set Int { s.univ }

/**
 * returns last index occupied by this sequence
 * (Returns the empty set if the sequence is empty)
 */
fun lastIdx [s: Int -> univ]: lone Int { ui/max[inds[s]] }

/**
 * returns the index after the last index
 * if this sequence is empty, returns 0
 * if this sequence is full, returns empty set
 */
fun afterLastIdx [s: Int -> univ] : lone Int { ui/min[seq/Int - inds[s]] }

/** returns first index at which given element appears or the empty set if it doesn't */
fun idxOf [s: Int -> univ, e: univ] : lone Int { ui/min[indsOf[s, e]] }

/** returns last index at which given element appears or the empty set if it doesn't */
fun lastIdxOf [s: Int -> univ, e: univ] : lone Int { ui/max[indsOf[s, e]] }

/** returns set of indices at which given element appears or the empty set if it doesn't */
fun indsOf [s: Int -> univ, e: univ] : set Int { s.e }

/**
 * return the result of appending e to the end of s
 * (returns s if s exhausted seq/Int)
 */
fun add [s: Int -> univ, e: univ] : s + (seq/Int->e) {
  setAt[s, afterLastIdx[s], e]
}

/**
 * returns the result of setting the value at index i in sequence to e
 * Precondition: 0 <= i < #s
 */
fun setAt [s: Int -> univ, i: Int, e: univ] : s + (seq/Int->e) {
  s ++ i -> e
}

/**
 * returns the result of inserting value e at index i
 * (if sequence was full, the original last element will be removed first)
 * Precondition: 0 <= i <= #s
 */
fun insert [s: Int -> univ, i: Int, e: univ] : s + (seq/Int->e) {
  seq/Int <: ((ui/prevs[i] <: s) + (i->e) + ui/prev.((ui/nexts[i] + i) <: s))
}

/**
 * returns the result of deleting the value at index i
 * Precondition: 0 <= i < #s
 */
fun delete[s: Int -> univ, i: Int] : s {
  (ui/prevs[i] <: s) + (ui/next).(ui/nexts[i] <: s)
}

/**
 * appended is the result of appending s2 to s1
 * (If the resulting sequence is too long, it will be truncated)
 */
fun append [s1, s2: Int -> univ] : s1+s2 {
  let shift = {i', i: seq/Int | int[i'] = ui/add[int[i], ui/add[int[lastIdx[s1]], 1]] } |
    no s1 => s2 else (s1 + shift.s2)
}

/**
 * returns the subsequence of s between from and to, inclusive
 * Precondition: 0 <= from <= to < #s
 */
fun subseq [s: Int -> univ, from, to: Int] : s {
  let shift = {i', i: seq/Int | int[i'] = ui/sub[int[i], int[from]] } |
    shift.((seq/Int - ui/nexts[to]) <: s)
}
