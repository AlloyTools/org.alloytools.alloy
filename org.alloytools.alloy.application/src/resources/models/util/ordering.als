module util/ordering[exactly elem]

/*
 * Creates a single linear ordering over the atoms in elem. It also constrains all
 * the atoms to exist that are permitted by the scope on elem. That is, if the scope
 * on a signature S is 5, opening util/ordering[S] will force S to have 5 elements
 * and create a linear ordering over those five elements. The predicates and
 * functions below provide access to properties of the linear ordering, such as
 * which element is first in the ordering, or whether a given element precedes
 * another. You cannotcreate multiple linear orderings over the same signature with
 * this model. If you that functionality, try using the util/sequence module instead.
 *
 * Technical comment:
 * An important constraint: elem must contain all atoms permitted by the scope.
 * This is to let the analyzer optimize the analysis by setting all fields of each
 * instantiation of Ord to predefined values: e.g. by setting 'last' to the highest
 * atom of elem and by setting 'next' to {<T0,T1>,<T1,T2>,...<Tn-1,Tn>}, where n is
 * the scope of elem. Without this constraint, it might not be true that Ord.last is
 * a subset of elem, and that the domain and range of Ord.next lie inside elem.
 *
 * author: Ilya Shlyakhter
 * revisions: Daniel jackson
 */

private one sig Ord {
   First: set elem,
   Next: elem -> elem
} {
   pred/totalOrder[elem,First,Next]
}

/** first */
fun first: one elem { Ord.First }

/** last */
fun last: one elem { elem - (next.elem) }

/** return a mapping from each element to its predecessor */
fun prev : elem->elem { ~(Ord.Next) }

/** return a mapping from each element to its successor */
fun next : elem->elem { Ord.Next }

/** return elements prior to e in the ordering */
fun prevs [e: elem]: set elem { e.^(~(Ord.Next)) }

/** return elements following e in the ordering */
fun nexts [e: elem]: set elem { e.^(Ord.Next) }

/** e1 is less than e2 in the ordering */
pred lt [e1, e2: elem] { e1 in prevs[e2] }

/** e1 is greater than e2 in the ordering */
pred gt [e1, e2: elem] { e1 in nexts[e2] }

/** e1 is less than or equal to e2 in the ordering */
pred lte [e1, e2: elem] { e1=e2 || lt [e1,e2] }

/** e1 is greater than or equal to e2 in the ordering */
pred gte [e1, e2: elem] { e1=e2 || gt [e1,e2] }

/** returns the larger of the two elements in the ordering */
fun larger [e1, e2: elem]: elem { lt[e1,e2] => e2 else e1 }

/** returns the smaller of the two elements in the ordering */
fun smaller [e1, e2: elem]: elem { lt[e1,e2] => e1 else e2 }

/**
 * returns the largest element in es
 * or the empty set if es is empty
 */
fun max [es: set elem]: lone elem { es - es.^(~(Ord.Next)) }

/**
 * returns the smallest element in es
 * or the empty set if es is empty
 */
fun min [es: set elem]: lone elem { es - es.^(Ord.Next) }

assert correct {
  let mynext = Ord.Next |
  let myprev = ~mynext | {
     ( all b:elem | (lone b.next) && (lone b.prev) && (b !in b.^mynext) )
     ( (no first.prev) && (no last.next) )
     ( all b:elem | (b!=first && b!=last) => (one b.prev && one b.next) )
     ( !one elem => (one first && one last && first!=last && one first.next && one last.prev) )
     ( one elem => (first=elem && last=elem && no myprev && no mynext) )
     ( myprev=~mynext )
     ( elem = first.*mynext )
     (all disj a,b:elem | a in b.^mynext or a in b.^myprev)
     (no disj a,b:elem | a in b.^mynext and a in b.^myprev)
     (all disj a,b,c:elem | (b in a.^mynext and c in b.^mynext) =>(c in a.^mynext))
     (all disj a,b,c:elem | (b in a.^myprev and c in b.^myprev) =>(c in a.^myprev))
  }
}
run {} for exactly 0 elem expect 0
run {} for exactly 1 elem expect 1
run {} for exactly 2 elem expect 1
run {} for exactly 3 elem expect 1
run {} for exactly 4 elem expect 1
check correct for exactly 0 elem
check correct for exactly 1 elem
check correct for exactly 2 elem
check correct for exactly 3 elem
check correct for exactly 4 elem
check correct for exactly 5 elem
