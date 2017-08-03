module examples/algorithms/s_ringlead

/*
 * Model of leader election on a ring.
 *
 * Each process has a unique ID, IDs are ordered. The algorithm
 * elects the process with the highest ID the leader, as follows.
 * First, each process sends its own ID to its right neighbor.
 * Then, whenever a process receives an ID, if the ID is greater
 * than the process' own ID it forwards the ID to its right
 * neighbor, otherwise does nothing. When a process receives its
 * own ID that process is the leader.
 *
 * Note: This file needs higher order quantifiers turned on.
 */

open util/ordering[State] as so
open util/ordering[Process] as po
open util/graph[Process] as graph

sig Process {
  rightNeighbor: Process
}

sig State {
  // buffer which the right neighbor can read from
  buffer: Process -> Process,
  //sends, reads: Process -> Process,
  runs: set Process,
  leader: set Process
}

fact DefineRing {
  graph/ring[rightNeighbor]
}

fact InitialState {
  no so/first.buffer
  no so/first.leader
  Process in so/first.runs
}


fact CleanupLast {
  let ls = so/last |
    no ls.runs
}

pred ValidTrans2[s, s': State] {
  all p : s.runs | VT2Helper[p,s,s']
  all p : Process - s.runs | NOP2[p,s,s']
  NoMagicMsg[s,s']

}

pred NoMagicMsg[s, s' : State] {
    // no magically appearing messages
    all p : Process, m : s'.buffer[p] |
      m in s.buffer[p] || (!NOP2[p,s,s'] &&
                            ((s = so/first && m = p) ||
                             (s != so/first && m in s.buffer[p.~rightNeighbor]
                              && m !in s'.buffer[p.~rightNeighbor] && po/gt[m,p])))
}

pred PossTrans[s, s' : State] {
  all p : Process | VT2Helper[p,s,s'] || NOP2[p,s,s']
  NoMagicMsg[s,s']
}

pred VT2Helper[p : Process, s, s' : State] {
    (
      let readable=s.buffer[p.~rightNeighbor] |
        (s = so/first) => {
          p = s'.buffer[p]
          readable in s'.buffer[p.~rightNeighbor]
          p !in s'.leader
        } else {
          (some readable) => {
           some m : set readable | {
             m !in s'.buffer[p.~rightNeighbor]
             // nothing else gets deleted
             readable - m in s'.buffer[p.~rightNeighbor]
             { m': m | po/gt[m',p] } /*m & nexts(p)*/ in s'.buffer[p]
             p in s'.leader iff (p in s.leader || p in m)
           }
          } else NOP2[p,s,s']
        }
    )
}

pred NOP2[p : Process, s,s': State] {
  p in s'.leader iff p in s.leader
  // no reads
  s.buffer[p.~rightNeighbor] in s'.buffer[p.~rightNeighbor]
  // no sends
  s'.buffer[p] in s.buffer[p]
}

pred Preconds[p : Process, s : State] {
  s = so/first || some s.buffer[p.~rightNeighbor]
}

fact TransIfPossible {
  all s : State - so/last |
    (all p : Process | NOP2[p, s, so/next[s]]) =>
      (all p : Process | !Preconds[p,s])
}

fact LegalTrans {
  all s : State - so/last |
    let s' = so/next[s] |
      ValidTrans2[s,s']
}

pred EquivStates[s, s': State] {
  s.buffer = s'.buffer
  s.leader = s'.leader
}

assert Safety {
  all s : State | lone s.leader
}

pred Legit[s : State] {
  one s.leader
}

pred BadLivenessTrace {
  all s : State | !Legit[s]
  let ls = so/last |
    some s : State - ls | {
      EquivStates[s, ls]
      Process in (so/nexts[s] + s).runs
    }
}

pred TraceWithoutLoop  {
  all t1, t2 : State | t1!=t2 => !EquivStates[t1,t2]
  all s, s' : State | (s' in (so/nexts[s] - so/next[s])) => !PossTrans[s,s']
  all s : State | !Legit[s]
}

pred AltTrans  {
  SomeLeader
}

pred SomeLeader { some State.leader }

run BadLivenessTrace for 3 but 8 State expect 0
run SomeLeader for 4 but 6 State expect 1
check Safety for 7 expect 0
// run TraceWithoutLoop for 5 but 13 State expect 1
run AltTrans for 5 but 8 State expect 1
