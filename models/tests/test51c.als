module tests/test51 -- example created by Emina Torlak on behalf of Mr. X

open tests/test51e as expansion

------------ Expansion is deterministic ------------
assert Determinism {
 all e: Expansion | lone e.next
}

check Determinism for 5 expect 0

------------ An expanded route contains only places. ------------
assert PlacesOnly {
  all e: Expansion | e.expandedRoute.elements in Place
}

check PlacesOnly for 4 expect 0

------------ Errors terminate expansion. ------------
assert EndOnError {
  all e: Expansion | some e.error => no e.next
}

check EndOnError for 5 expect 0

------------ Expansion is acyclic. ------------
assert Acyclic {
  no ^(next & Expansion->Expansion) & iden
}

check Acyclic for 5 expect 0

------------ Expansion distributes through concatenation. ------------

fun expand[r: Route]: Route {
 {e: Expansion | e.proposedRoute = r and no e.next }.expandedRoute
}

assert Distributivity {
  all s, t, r: Route |
   s.concat [t, r] => expand[s].concat[expand[t], expand[r]]
}

check Distributivity for 3 expect 1
