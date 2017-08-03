module tests/test51 -- example created by Emina Torlak on behalf of Mr. X

------------ Points, Features, and Places ------------

-- A physical point on the ground, on a map, etc.  A point
-- may be contained in a place.
sig Point {
  place: lone Place
}

-- A major geographic feature:  a place or a road.
abstract sig Feature {}

-- A place is defined by a set of points.
sig Place extends Feature {}

-- Returns the set of all points contained in this place
fun points [p: Place] : set Point { place.p }
------------ Roads ------------

-- A road is defined by a sequence of points.
-- Each point on a road may have connections to features.
sig Road extends Feature {
  geography: seq Point,
  connections: geography[Int] -> Feature
}{
  all p: Point | lone geography.p   -- the points on a road are unique
}

-- Returns the set of all points that define this road.
fun points [r: Road] : set Point { r.geography[Int] }

-- Returns the first point on this road.
fun first [r: Road] : lone Point { r.geography.first }

-- Returns the last point on this road.
fun last [r: Road] : lone Point { r.geography.last }

-- True if p1 is closer to the beginning of this road than p2
pred closer [r: Road, p1, p2: Point] {
  let geo = r.geography | lt[geo.p1, geo.p2]
}

-- True if p1 is farther from the beginning of this road than p2
pred farther [r: Road, p1, p2: Point] {
  let geo = r.geography | gt[geo.p1, geo.p2]
}

-- Returns the point closest to the beginning of this road,
-- or the empty set if none of the given points is on this road.
fun closest [r: Road, points: set Point] : lone Point {
  let geo = r.geography | geo[min[geo.points]]
}

-- Returns the point farthest from the beginning of this road,
-- or the empty set if none of the given points is on the road.
fun farthest [r: Road, points: set Point] : lone Point {
  let geo = r.geography | geo[max[geo.points]]
}

-- Returns the point that immediately precedes the given point
-- on this road, if any.
fun predecessor[r: Road, point: Point] : lone Point {
  let geo = r.geography | geo[prev[geo.point]]
}

-- Returns the point that immediately follows the given point
-- on this road, if any.
fun successor [r: Road, point: Point] : lone Point {
  let geo = r.geography | geo[next[geo.point]]
}

-- Returns the set of points on this road that
-- precede the given point
fun before [r: Road, point: Point] : set Point {
  let geo = r.geography | geo[prevs[geo.point]]
}

-- Returns the set of points on this road that
-- succeed the given point
fun after [r: Road, point: Point] : set Point {
  let geo = r.geography | geo[nexts[geo.point]]
}

-- Returns the set of all points on this road that have a connection to
-- the given feature.  A connection to a feature is a point on this road
-- that is connected to the given feature or that is contained in the feature.
fun connections[r: Road, feature: Feature]: set Point {
  r.connections.feature + r.points & (feature<:Place).points
}
