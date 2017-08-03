module tests/test // Bugpost by Daniel Jackson

open util/sequence[Element] as ProposedRoute
open util/sequence[Place] as ExpandedRoute
open util/sequence[PlaceOnRoad] as Road

------------ Elements and Routes ------------

abstract sig Element {
  name: Place + Road/Seq
}

sig PlaceElement, RoadElement extends Element {}

fact element_correspondence {
  PlaceElement.name in Place and
  RoadElement.name in Road/Seq
}


pred SyntacticallyValidProposedRoute [s: ProposedRoute/Seq] {
   not lone s.inds and
   s.first in PlaceElement and
   s.last in PlaceElement
}


------------ Geography ------------

sig Place {}

sig PlaceOnRoad extends Place {
  place: Place,
  connectsToRoad: set Road/Seq,
  connectsToPlace: set Place
}


------------ Expanded Routes ------------

sig Expansion {
  proposedRoute: ProposedRoute/Seq,
  currentIndex: ProposedRoute/SeqIdx,
  expandedRoute: ExpandedRoute/Seq,
  error: lone Error
}

abstract sig Error {}
one sig SyntaxError, NoConnection extends Error {}


pred startExpansion(p: ProposedRoute/Seq, e: Expansion) {
  e.proposedRoute = p and
  e.currentIndex = ProposedRoute/firstIdx and
  no e.expandedRoute.inds and
  e.error = (p.SyntacticallyValidProposedRoute => none else SyntaxError)
}

pred expand(e, e': Expansion) {
  no e.error and
  e'.proposedRoute = e.proposedRoute and
  e'.currentIndex = ProposedRoute/next[e.currentIndex] and
  (expandPlace[e, e'] or expandRoad[e, e'])
}

pred expandPlace(e, e': Expansion) {
  let currentElem = e.proposedRoute.at[e.currentIndex], p = currentElem.name |
   currentElem in PlaceElement and
   (p = e.expandedRoute.last =>
    e'.expandedRoute = e.expandedRoute else
    e.expandedRoute.add[p, e'.expandedRoute] ) and
   no e'.error
}

pred addPlaces(eroute, eroute': ExpandedRoute/Seq, road: Road/Seq, start, end: Road/SeqIdx) {
  Road/lte[start, end] and
  eroute'.startsWith[eroute] and
  (let roadInds = start + Road/nexts[start] & Road/prevs[end] + end |
   (all roadIdx: roadInds | some expIdx: ExpandedRoute/nexts[eroute.lastIdx] |
    eroute'.at[expIdx] = road.at[roadIdx] and
    #(Road/prevs[roadIdx] - Road/prevs[start]) =
    #(ExpandedRoute/prevs[expIdx] - ExpandedRoute/prevs[eroute.afterLastIdx])) and
   #eroute'.inds = #(eroute.inds + roadInds)
  )
}

pred expandRoad(e, e': Expansion) {
  let currentElem = e.proposedRoute.at[e.currentIndex], r = currentElem.name |
   currentElem in RoadElement and
   (let entries = findConnections[r, e.proposedRoute.at[ProposedRoute/prev[e.currentIndex]]],
    exits = findConnections[r, e.proposedRoute.at[ProposedRoute/next[e.currentIndex]]] |
    ((no entries or no exits) and e'.error = NoConnection)  or
    ((let entry = Road/min[entries], exit = Road/min[exits],
      start = Road/min[entry+exit], end = Road/max[entry+exit] |
      r.at[start] = e.expandedRoute.last =>
       addPlaces[e.expandedRoute, e'.expandedRoute, r, Road/next[start], end] else
       addPlaces[e.expandedRoute, e'.expandedRoute, r, start, end]) and
     no e'.error)
   )
}

fun findConnections(road: Road/Seq, elem: Element): Road/SeqIdx {
  findConnectionsPlace[road, elem] + findConnectionsRoad[road, elem]
}

fun findConnectionsPlace(road: Road/Seq, elem: PlaceElement): Road/SeqIdx {
  road.indsOf[elem.name] + road.indsOf[connectsToPlace.(elem.name)]
}

fun findConnectionsRoad(road: Road/Seq, elem: RoadElement): Road/SeqIdx {
  road.indsOf[connectsToRoad.(elem.name)]
}

sig ExpansionProcess {
  step: Expansion -> Expansion
}{
  (all e: step.Expansion | expand[e, step[e]]) and
  (all last: Expansion.step | no step[last] =>
   (some last.error or last.currentIndex !in last.proposedRoute.inds)) and
  (all first: step.Expansion | no step.first => startExpansion[first.proposedRoute, first] )
}

------------ test geography ------------
one sig M4, A34, A40 extends Road/Seq {}
one sig Oxford, OxfordW, Newbury, NewburyRoundabout, Burford, Swindon, Bicester extends Place {}
one sig a34b, a34o, a34n, a40o, a40b, m4s, m4n extends PlaceOnRoad {}

pred test() {
  (let first = Road/firstIdx, second = Road/next[first], third = Road/next[second] |
    M4.seqElems = first -> m4s + second -> m4n and
    A34.seqElems = first -> a34b +second -> a34o + third -> a34n and
    A40.seqElems = first -> a40b + second -> a40o ) and
  place = a34b -> Bicester + a34o -> Oxford + a34n -> NewburyRoundabout +
              a40o -> OxfordW + a40b -> Burford + m4s -> Swindon + m4n -> NewburyRoundabout and
  connectsToRoad = a40o -> A34 + a34o -> A40 and
  connectsToPlace = a40b -> Swindon + m4n -> Newbury + a34n -> Newbury
}

run { test and some step  } for 4 but
3 Road/Seq, 14 Place, 7 PlaceOnRoad, 1 ProposedRoute/Seq, 1 ExpansionProcess, 3 Expansion
expect 1

------------ analyze properties ------------

assert ExpansionDeterministic {
  all p: ExpansionProcess | p.step in Expansion -> lone Expansion
  }

check ExpansionDeterministic for 5 but 1 ExpansionProcess expect 1
