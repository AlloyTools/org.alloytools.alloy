module tests/test51 -- example created by Emina Torlak on behalf of Mr. X

open tests/test51r as routes

------------ Errors ------------

-- An enum of errors that can occur during route expansion
abstract sig Error {}
one sig NoConnection, SyntaxError extends Error {}

------------ Expansions ------------

-- Encapsulation of one step in the process of expanding a proposed route.
sig Expansion {
  proposedRoute, expandedRoute: Route,
  currentIndex: Int,
  error: lone Error,
  next: set Expansion
}

-- Facts about expansions.
fact ExpansionFacts  {
  (all e: Expansion, e': e.next | e.expand[e']) and         -- expansions are related by the expand op

  (all e: Expansion | no next.e <=> e.start) and            -- if no predecessor, e is the initial expansion

  (all e: Expansion | no e.next <=> (some e.error or        -- if no successor, e is the last expansion
    e.currentIndex !in e.proposedRoute.inds)) and

  (all e1, e2: Expansion | e1.eq[e2] => e1 = e2)        -- expansions are cannonical
}

-- Returns the feature that is being expanded.
fun currentFeature [e: Expansion]: lone Feature {
  e.proposedRoute.at[e.currentIndex]
}

-- Returns the feature that will be expanded in the next step.
fun nextFeature [e:Expansion] : lone Feature {
  e.proposedRoute.at[next[e.currentIndex]]
}

-- Returns the feature that has been expanded in the previous step.
fun prevFeature [e:Expansion] : lone Feature {
  e.proposedRoute.at[prev[e.currentIndex]]
}

-- True if the given expansion has the same field values as this one.
pred eq [e: Expansion, other: Expansion] {
  e.proposedRoute = other.proposedRoute and
  e.currentIndex = other.currentIndex and
  e.expandedRoute = other.expandedRoute and
  e.error = other.error
}

-- True if the given expansion is the first step in the process of expanding this.proposedRoute
pred start [e: Expansion] {
  e.currentIndex = 0 and
  no e.expandedRoute.inds and
  e.error = (syntacticallyValidProposedRoute[e.proposedRoute] => none else SyntaxError)
}

-- True if e'  follows this in the process of expanding this.proposedRoute
pred expand [e, e': Expansion] {
  no e.error and
  e'.proposedRoute = e.proposedRoute and
  e'.currentIndex =next[e.currentIndex] and
  (e.expandPlace[e'] or e.expandRoad[e'])
}

-- True if e' is obtained by expanding this.expandedRoute with the place at this.currentIndex
pred expandPlace [e, e': Expansion] {
  let p = Place & (e.currentFeature) |
   e.currentFeature in Place and
   (p = e.expandedRoute.last =>
    e'.expandedRoute = e.expandedRoute else
    e.expandedRoute.addPlace[p, e'.expandedRoute] ) and
   no e'.error
}

-- True if e' is obtained by expanding this.expandedRoute with the places on the road at this.currentIndex
pred expandRoad [e, e': Expansion] {
  let r = Road & (e.currentFeature) |
   e.currentFeature in Road and
   (let entry = r.closest[r.connections[e.prevFeature]], exit = r.closest[r.connections[e.nextFeature]] |
    (no entry or no exit) =>
    (e'.error = NoConnection and e'.expandedRoute = e.expandedRoute) else
    ((let start =r.closest[entry+exit], end = r.farthest[entry+exit] |
      start.place = e.expandedRoute.last =>
      e.expandedRoute.addPlaces[r, r.successor[start], end, e'.expandedRoute] else
      e.expandedRoute.addPlaces[r, start, end, e'.expandedRoute]) and
     no e'.error)
   )
}
