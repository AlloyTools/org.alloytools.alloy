/*
 * a simple list module
 * which demonstrates how to create predicates and fields that mirror each other
 *   thus allowing recursive constraints (even though recursive predicates are not
 *   currently supported by Alloy)
 * author: Robert Seater
 */

module list

sig Thing {}
fact NoStrayThings {Thing in List.car}

abstract sig List {
    equivTo: set List,
    prefixes: set List
    }
sig NonEmptyList extends List {
    car: one Thing,
    cdr: one List
    }
sig EmptyList extends List {}

pred isFinite [L:List] {some e: EmptyList | e in L.*cdr}
fact finite {all L: List | isFinite[L]}

fact Equivalence {
    all a,b: List | (a in b.equivTo) <=> ((a.car = b.car and b.cdr in a.cdr.equivTo) and (#a.*cdr = #b.*cdr))
    }
assert reflexive {all L: List | L in L.equivTo}
check reflexive for 6 expect 0
assert symmetric {all a,b: List | a in b.equivTo <=> b in a.equivTo}
check symmetric for 6 expect 0
assert empties {all a,b: EmptyList | a in b.equivTo}
check empties for 6 expect 0

fact prefix { //a is a prefix of b
    all e: EmptyList, L:List | e in L.prefixes
    all a,b: NonEmptyList | (a in b.prefixes) <=> (a.car = b.car
                                                and a.cdr in b.cdr.prefixes
                                                and #a.*cdr < #b.*cdr)
}

pred show {
    some a, b: NonEmptyList | a!=b && b in a.prefixes
    }
run show for 4 expect 1

