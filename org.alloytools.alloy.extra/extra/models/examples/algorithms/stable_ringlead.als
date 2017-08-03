module examples/algorithms/stable_ringlead

/*
 * Huang's self-stabilizing leader-election algorithm
 * for rings.
 */

open util/ordering[Process] as po
open util/ordering[Val] as vo
open util/ordering[State] as so
open util/graph[Process] as graph

sig Process {
  rightNeighbor: Process
}

sig Val {
  nextVal : Val
}

fact {
  graph/ring[rightNeighbor]
  vo/next + (vo/last -> vo/first) = nextVal
  # Val = # Process
}

sig State {
  val : Process -> one Val,
  running : set Process
  // for visualization
  //leader : set Process
} {
  //leader = { p : Process | LeaderAtState(p, this) }
}

fact {
  no so/last.running
}

fun LeadersAtState[t : State] : set Process {
  { p : Process | LeaderAtState[p,t] }
}

pred LeaderAtState[p : Process, t : State] { ValAtState[p,t] = vo/first }

fun ValAtState[p : Process, t : State] : Val { t.val[p] }

fun LeftValAtState[p : Process, t : State] : Val { t.val[p.~rightNeighbor] }

fun RightValAtState[p : Process, t : State] : Val { t.val[p.rightNeighbor] }

fun XAtState[p : Process, t : State] : Int {
  g[LeftValAtState[p,t],ValAtState[p,t]]
}

fun YAtState[p : Process, t : State] : Int {
  g[ValAtState[p,t],RightValAtState[p,t]]
}

fun g[a, b : Val] : Int {
  (a = b) => Int[# Val] else minus[b,a]
}

fun minus[v1, v2 : Val] : Int {
  Int[ (v1 = v2) => 0
        else vo/gt[v1, v2] => (# (vo/nexts[v2] & vo/prevs[v1] + v1))
        else (# (Val - (vo/nexts[v1] & vo/prevs[v2] + v1)))
  ]
}

fun Trans[oldVal : Val, x, y : Int] : Val {
  ((int x = int y && int y = # Val) || (int x < int y)) => oldVal.nextVal else oldVal
}

pred OneAtATimeTrans {
  all tp: State - so/last |
    let tn = so/next[tp] |
      some p : Process | {
        tp.running = p
        TransHelper[p,tp,tn]
        all other : Process - p |
          ValAtState[other,tn] = ValAtState[other,tp]
      }
}

pred DDaemonTrans {
  all tp: State - so/last |
    let tn = so/next[tp] | {
      some tp.running
      all p : tp.running | TransHelper[p,tp,tn]
      all other : Process - tp.running |
        ValAtState[other,tn] = ValAtState[other,tp]
    }
}

pred TransHelper[p : Process, tp, tn : State] {
        let oldVal = ValAtState[p, tp],
            newVal = ValAtState[p, tn],
            x = XAtState[p, tp],
            y = YAtState[p,tp] |
          newVal = Trans[oldVal, x, y]

}

pred StateTrans[s, s' : State] {
  all p : Process |
    TransHelper[p, s, s'] || ValAtState[p,s] = ValAtState[p,s']
}



pred CBadLivenessTrace  {
  OneAtATimeTrans
  BadLivenessHelper
}

pred DBadLivenessTrace {
  DDaemonTrans
  BadLivenessHelper
}

pred BadLivenessHelper {
  let ls = so/last |
    some s : State - ls | {
      s.val = ls.val
      // fair
      Process in (so/nexts[s] + s - ls).running
    }
    all s : State | ! Legit[s]
  }

pred CTraceWithoutLoop {
  OneAtATimeTrans
  all t, t' : State | t!=t' => t.val != t'.val
}

pred DTraceWithoutLoop {
  DDaemonTrans
  all t, t' : State | t!=t' => {
    t.val != t'.val
    (t' in so/nexts[t] && t' != so/next[t]) => !StateTrans[t,t']
  }
  all t : State | !Legit[t]
}

pred ConvergingRun  {
  OneAtATimeTrans
  !Legit[so/first]
  some t : State | Legit[t]
}

pred OnlyFairLoops {
  OneAtATimeTrans
  all s, s' : State |
   (s' in so/nexts[s] && s'.val = s.val) =>
     (let loopStates = (so/nexts[s] & so/prevs[s']) + s + s' | Process in loopStates.running)
}

assert CMustConverge {
  OnlyFairLoops => (some s : State | Legit[s])
}

pred Legit [s : State] {
  one LeadersAtState[s]
  all p : Process | {
    int XAtState[p,s] < # Val
    int YAtState[p,s] < # Val
  }
  all p, p' : Process | {
    int XAtState[p,s] = int XAtState[p',s]
    int YAtState[p,s] = int YAtState[p',s]
  }
}

run ConvergingRun for 3 but 4 State expect 1
run DTraceWithoutLoop for 3 but 4 State expect 1
run DBadLivenessTrace for 3 but 4 State expect 1
run CTraceWithoutLoop for 3 but 5 State expect 0
run CBadLivenessTrace for 4 but 5 State expect 1
check CMustConverge for 3 but 4 State expect 0
