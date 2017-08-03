module examples/toys/life

/*
 * John Conway's Game of Life
 *
 * For a detailed description, see:
 *  http://www.math.com/students/wonders/life/life.html
 *
 * authors: Bill Thies, Manu Sridharan
 */

open util/ordering[State] as ord

sig Point {
  right: lone Point,
  below: lone Point
}

fact Acyclic {
  all p: Point | p !in p.^(right + below)
}

one sig Root extends Point {}

fact InnerSquaresCommute {
  all p: Point {
    p.below.right = p.right.below
    some p.below && some p.right => some p.below.right
  }
}

fact TopRow {
  all p: Point - Root | no p.~below => # p.*below = # Root.*below
}

fact Connected {
  Root.*(right + below) = Point
}

pred Square {
  # Root.*right = # Root.*below
}

run Square for 6 Point, 3 State expect 1

pred Rectangle {}

sig State {
  live : set Point
}

fun Neighbors[p : Point] : set Point {
  p.right + p.right.below + p.below
              + p.below.~right + p.~right
              + p.~right.~below + p.~below +
              p.~below.right
}

fun LiveNeighborsInState[p : Point, s : State] : set Point {
  Neighbors[p] & s.live
}

pred Trans[pre, post: State, p : Point] {
   let preLive = LiveNeighborsInState[p,pre] |
    // dead cell w/ 3 live neighbors becomes live
    (p !in pre.live && # preLive = 3) =>
    p in post.live
  else (
    // live cell w/ 2 or 3 live neighbors stays alive
    (p in pre.live && (# preLive = 2 || # preLive = 3)) =>
      p in post.live else p !in post.live
    )
}

fact ValidTrans {
  all pre : State - ord/last |
    let post = ord/next[pre] |
      all p : Point |
        Trans[pre,post,p]
}

pred Show {}

// slow
run Show for exactly 12 Point, 3 State expect 1

// a small but interesting example
pred interesting {
	some State.live
	some Point - State.live
	some right
	some below
}
run interesting for exactly 6 Point, 3 State expect 1