module tests/test51 -- example created by Emina Torlak on behalf of Mr. X

open tests/test51g as geography

------------ Routes ------------

-- A route is a defined by a sequence of features.
sig Route {
  features: seq Feature
}
-- Facts about routes
fact RouteFacts {
  all r1, r2: Route | r1.features = r2.features => r1 = r2  -- routes are canonical
}

-- Defines a proposed route as syntactically valid if it has at least two features,
-- and if the first and last features are places.
pred syntacticallyValidProposedRoute [r: Route] {
   not lone r.features and
   r.first in Place and
   r.last in Place
}

-- Returns the set of features that comprise this route.
fun elements [r: Route] : set Feature { r.features[Int] }

-- Returns the set of indices that comprise this route.
fun inds [r: Route] : set Int { r.features.Feature }

-- Returns the first feature of this route.
fun first [r: Route] : lone Feature { r.features.first }

-- Returns the last feature of this route.
fun last [r: Route] : lone Feature { r.features.last }

-- Returns the feature at the given index.
fun at [r: Route, idx: Int] : lone Feature { r.features[idx] }

-- Constrains route' to have this route as its prefix and the places containing the points
-- between start and end, inclusive, as its suffix.
pred addPlaces [r: Route, road: Road, start, end: Point, route': Route] {

 (start = end or road.closer[start, end]) and
 route'.features = append[r.features, subseq[road.geography, road.geography.start, road.geography.end].place ]

}

-- Constraints route' to have this route and its prefix and the given place as its suffix.s
pred addPlace [r: Route, place: Place, route': Route] {
  route'.features = r.features.add[place]
}

-- Constraints route' to be the concatenation of this and the given route.
pred concat [r: Route, other: Route, route': Route] {
  route'.features = r.features.append[other.features]
}
