module examples/toys/railway

/*
 * A simple model of a railway system. Trains sit on segments of tracks
 * and segments overlap one another. It shows a that simple gate policy
 * does not ensure train safety.
 *
 * author: Daniel Jackson
 */

sig Seg {next, overlaps: set Seg}
fact {all s: Seg | s in s.overlaps}
fact {all s1, s2: Seg | s1 in s2.overlaps => s2 in s1.overlaps}

sig Train {}
sig GateState {closed: set Seg}
sig TrainState {on: Train -> lone Seg, occupied: set Seg}
fact {all x: TrainState |
  x.occupied = {s: Seg | some t: Train | t.(x.on) = s}
  }

pred Safe [x: TrainState] {all s: Seg | lone s.overlaps.~(x.on)}

pred MayMove [g: GateState, x: TrainState, ts: set Train] {
  no ts.(x.on) & g.closed
  }

pred TrainsMove [x, x': TrainState, ts: set Train] {
  all t: ts | t.(x'.on) in t.(x.on).next
  all t: Train - ts | t.(x'.on) = t.(x.on)
  }

pred GatePolicy [g: GateState, x: TrainState] {
  x.occupied.overlaps.~next in g.closed
  all s1, s2: Seg | some s1.next.overlaps & s2.next => lone (s1+s2) - g.closed
}

assert PolicyWorks {
  all x, x': TrainState, g: GateState, ts: set Train |
    {MayMove [g, x, ts]
    TrainsMove [x, x', ts]
    Safe [x]
    GatePolicy [g, x]
    } => Safe [x']
  }

-- has counterexample in scope of 4
check PolicyWorks for 2 Train, 1 GateState, 2 TrainState, 4 Seg expect 1

pred TrainsMoveLegal [x, x': TrainState, g: GateState, ts: set Train] {
  TrainsMove [x, x', ts]
  MayMove [g, x, ts]
  GatePolicy [g, x]
  }
run TrainsMoveLegal for 3 expect 1



// DEFINED VARIABLES
// Defined variables are uncalled, no-argument functions.
// They are helpful for getting good visualization.
fun contains [] : TrainState -> Seg -> Train {
	{state: TrainState, seg: Seg, train: Train | seg = train.(state.on)}
}
