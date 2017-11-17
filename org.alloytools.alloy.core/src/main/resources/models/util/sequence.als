module util/sequence[elem]

/*
 * Creates sequences (or lists) of elements. The ordered signature SeqIdx
 * represents the indexes at which elements can be located, and a sequence
 * is modeled as a mapping from indexes to elements. Empty sequences are
 * allowed, and a sequence may have a single element appear multiple times.
 * Maximum length of a sequence is determined by the scope of SeqIdx.
 *
 * Sequences always cover an initial segment of SeqIdx. That is, every
 * sequence (except the empty sequence) begins at the first SeqIdx and does
 * not have gaps in indexes that it covers. In other words, if a sequence has
 * its last element at index i, then the sequence has elements at all the
 * indexes that precede i.
 *
 * Oftentimes, a model will need to require that all sequences that could
 * exist, do exist. Calling the allExist predicate will ensure that that there is
 * a Seq atom for each possible sequences of elements with length less than
 * or equal to the scope of SeqIdx.
 *
 * The functions and predicates at the bottom of this module provide all
 * functionality of util/ordering on SeqIdx.
 *
 * revisions: Greg Dennis
 */

open util/ordering[SeqIdx] as ord

sig SeqIdx {}

sig Seq {
   seqElems: SeqIdx -> lone elem
}
{
  // Ensure that elems covers only an initial segment of SeqIdx,
  // equal to the length of the signature
  all i: SeqIdx - ord/first | some i.seqElems => some ord/prev[i].seqElems
}

/** no two sequences are identical */
fact canonicalizeSeqs {
  no s1, s2: Seq | s1!=s2 && s1.seqElems=s2.seqElems
}

/** invoke if you want none of the sequences to have duplicates */
pred noDuplicates {
  all s: Seq | !s.hasDups
}

/** invoke if you want all sequences within scope to exist */
pred allExist {
  (some s: Seq | s.isEmpty) &&
  (all s: Seq | SeqIdx !in s.inds => (all e: elem | some s': Seq | s.add[e, s']))
}

/** invoke if you want all sequences within scope with no duplicates */
pred allExistNoDuplicates {
  some s: Seq | s.isEmpty
  all s: Seq {
    !s.hasDups
    SeqIdx !in s.inds => (all e: elem - s.elems | some s': Seq | s.add[e, s'])
  }
}

/** returns element at the given index */
fun at [s: Seq, i: SeqIdx]: lone elem { i.(s.seqElems) }

/** returns all the elements in this sequence */
fun elems [s: Seq]: set elem { SeqIdx.(s.seqElems) }

/** returns the first element in the sequence */
fun first [s:Seq]: lone elem { s.at[ord/first] }

/** returns the last element in the sequence */
fun last [s:Seq]: lone elem { s.at[s.lastIdx] }

/**
 * true if the argument is the "cdr" of this sequence
 * false if this sequence is empty
 */
pred rest [s, r: Seq] {
   !s.isEmpty
   all i: SeqIdx | r.at[i] = s.at[ord/next[i]]
}

/** true if the sequence is empty */
pred isEmpty [s:Seq] { no s.elems }

/** true if this sequence has duplicates */
pred hasDups [s:Seq] { # elems[s] < # inds[s] }

/** returns all the indices occupied by this sequence */
fun inds [s:Seq] : set SeqIdx { elem.~(s.seqElems) }

/** returns last index occupied by this sequence */
fun lastIdx [s:Seq] : lone SeqIdx { ord/max[s.inds] }

/**
 * returns the index after the last index
 * if this sequence is empty, returns the first index,
 * if this sequence is full, returns empty set
 */
fun afterLastIdx [s:Seq] : lone SeqIdx {
  ord/min[SeqIdx - s.inds]
}

/** returns first index at which given element appears or the empty set if it doesn't */
fun idxOf [s: Seq, e: elem] : lone SeqIdx { ord/min[s.indsOf[e]] }

/** returns last index at which given element appears or the empty set if it doesn't */
fun lastIdxOf [s: Seq, e: elem] : lone SeqIdx { ord/max[s.indsOf[e]] }

/** returns set of indices at which given element appears or the empty set if it doesn't */
fun indsOf [s: Seq, e: elem] : set SeqIdx { (s.seqElems).e }

/** true if this starts with prefix */
pred startsWith [s, prefix: Seq] {
  all i: prefix.inds | s.at[i] = prefix.at[i]
}

/** added is the result of appending e to the end of s */
pred add [s: Seq, e: elem, added: Seq] {
  added.startsWith[s]
  added.seqElems[s.afterLastIdx] = e
  #added.inds = #s.inds.add[1]
}

/** setted is the result of setting value at index i to e */
pred setAt [s: Seq, idx: SeqIdx, e: elem, setted: Seq] {
  setted.seqElems = s.seqElems ++ idx->e
}

/** inserts is the result of inserting value e at index i */
pred insert [s: Seq, idx: SeqIdx, e: elem, inserted: Seq] {
  inserted.at[idx] = e
  all i: ord/prevs[idx] | inserted.at[i] = s.at[i]
  all i: ord/nexts[idx] | inserted.at[i] = s.at[ord/prev[i]]
  #inserted.inds = #s.inds.add[1]
}

/** copies source into dest starting at destStart */
pred copy [source, dest: Seq, destStart: SeqIdx] {
  all sourceIdx : source.inds | some destIdx: SeqIdx {
    ord/gte[destIdx, destStart]
    dest.at[destIdx] = source.at[sourceIdx]
    #ord/prevs[sourceIdx] = #(ord/prevs[destIdx] - ord/prevs[destStart])
  }
}

/** appended is the result of appending s2 to s1 */
pred append [s1, s2, appended: Seq] {
  appended.startsWith[s1]
  copy[s2, appended, s1.afterLastIdx]
  #appended.inds = #s1.inds.add[#s2.inds]
}

/** sub is the subsequence of s between from and to, inclusive */
pred subseq [s, sub: Seq, from, to: SeqIdx] {
  ord/lte[from, to]
  copy[sub, s, from]
  #sub.inds = #(to + ord/prevs[to] - ord/prevs[from])
}

fun firstIdx: SeqIdx { ord/first }

fun finalIdx: SeqIdx { ord/last }
