module tests/test // Bugpost by Emina Torlak

open util/seqrel[Element] as sq

sig Name {}

abstract sig Element {
  name: Name
}

sig PlaceElement, RoadElement extends Element {}

sig ProposedRoute {
  elements: sq/SeqIdx -> Element
}

fact proposed_route_is_a_seq_of_elements {
  all route: ProposedRoute | sq/isSeq[route.elements]
}

sig SyntacticallyValidProposedRoute in ProposedRoute {}

fact syntactically_valid_if_both_ends_are_places {
  SyntacticallyValidProposedRoute =  { route: ProposedRoute |
   not lone route.elements and
   first[route.elements] in PlaceElement and
   sq/last[route.elements] in PlaceElement
}
}

run {some ProposedRoute } for 3 expect 1
