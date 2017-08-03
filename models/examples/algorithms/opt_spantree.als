module examples/algorithms/opt_spantree

/*
 * Direct specification of a distributed spanning tree algorithm
 * over arbitrary network topologies
 *
 * Each process has a parent and a level, both of which are
 * initally null. A distinct root node exists at which the
 * algorithm starts. In the first step, the root assigns itself
 * the level of zero and sends its level to its neighbors.
 * Subsequently, if a node reads a message with level k, it sets
 * its level to k+1, records the sender of the message as its
 * parent, and sends the level k+1 to its neighbors. Once a node
 * has set its level and parent, it ignores subsequent messages.
 * Eventually, the parent pointers will form a spanning tree,
 * rooted at Root.
 *
 * We model communication through a state-reading model, in which
 * nodes can directly read the state of their neighbors. Messages
 * are not explicity modelled. This makes no difference for this
 * algorithm since once a node sends a message, the state of the
 * node stays the same as the contents of the message.
 */

open util/ordering[Lvl] as lo
open util/ordering[State] as so
open util/graph[Process] as graph

sig Process {
  adj : set Process
}

one sig Root extends Process {}

// intuitively, the depth level at which
// a process resides in the spanning tree,
// with the root at level zero
sig Lvl {}

fact processGraph {
  graph/noSelfLoops[adj]     // for viz
  graph/undirected[adj]      // adjacency is symmetric
  Process in Root.*adj // everything reachable from root
}

sig State {
  // the set of processes which execute in this state.
  // used to allow flexibility in how many processes
  // run simultaneously
  runs : set Process,
  // the level of a process in this state
  lvl: Process -> lone Lvl,
  // who the process thinks is its parent in this state.
  // the parent pointers should eventually become
  // the spanning tree
  parent: Process -> lone Process
}

pred Init {
  // initially, the lvl and parent fields are blank
  let fs = so/first | {
    no fs.lvl
    no fs.parent
  }
}

// simple NOP transition
pred TRNop[p : Process, pre, post: State] {
  pre.lvl[p] = post.lvl[p]
  pre.parent[p] = post.parent[p]
}

// preconditions for a process to actually act
// in a certain pre-state
// used to preclude stalling of entire system
// for no reason (see TransIfPossible)
pred TRActPreConds[p : Process, pre : State] {
  // can't already have a level
  no pre.lvl[p]
  // must have a neighbor with a set level so
  // p can read it
  // Root doesn't need to read value from a
  // neighbor
  (p = Root || some pre.lvl[p.adj])
}

// transition which changes state of a process
pred TRAct[p : Process, pre, post : State] {
  // can't already have a level
  no pre.lvl[p]
  (p = Root) => {
    // the root sets its level to
    // 0, and has no parent pointer
    post.lvl[p] = lo/first
    no post.parent[p]
  } else {
    // choose some adjacent process
    // whose level is already set
    some adjProc: p.adj |
      let nLvl = pre.lvl[adjProc] | {
        some nLvl
        // p's parent is the adjacent
        // process, and p's level is one greater than
        // the level of the adjacent process (since
        // its one level deeper)
        post.lvl[p] = lo/next[nLvl]
        post.parent[p] = adjProc
      }
  }
}

pred Trans[p : Process, pre, post : State] {
  TRAct[p, pre, post] ||
  TRNop[p, pre, post]
}

fact TransIfPossible {
  // all processes do a nop transition in some
  // state only when no process can act because
  // preconditions are not met
  all s : State - so/last |
    (all p : Process | TRNop[p, s, so/next[s]]) =>
      (all p : Process | !TRActPreConds[p,s])
}

fact LegalTrans {
  Init
  all s : State - so/last |
    let s' = so/next[s] | {
      all p : Process |
        p in s.runs => Trans[p, s, s'] else TRNop[p,s,s']
    }
}

pred PossTrans[s, s' : State] {
  all p : Process | Trans[p,s,s']
}

pred SpanTreeAtState[s : State] {
  // all processes reachable through inverted parent pointers
  // from root (spanning)
  Process in Root.*~(s.parent)
  // parent relation is a tree (DAG)
  // we only need to check the DAG condition since there can
  // be at most one parent for a process (constrained by
  // multiplicity)
  graph/dag[~(s.parent)]
}

// show a run that produces a spanning tree
pred SuccessfulRun {
  SpanTreeAtState[so/last]
  all s : State - so/last | !SpanTreeAtState[s]
}

// show a trace without a loop
pred TraceWithoutLoop {
  all s, s' : State | s!=s' => {
    !EquivStates[s, s']
    (s' in so/nexts[s] && (s' != so/next[s])) => !PossTrans[s,s']
  }
  all s: State | !SpanTreeAtState[s]
}

// defines equivalent states
pred EquivStates[s, s' : State] {
  s.lvl = s'.lvl
  s.parent = s'.parent
}

// show a trace that violates liveness
pred BadLivenessTrace {
  // two different states equivalent (loop)
  some s, s' : State | s!=s' && EquivStates[s, s']
  all s : State | !SpanTreeAtState[s]
}

// check that once spanning tree is constructed,
// it remains
assert Closure {
  all s : State - so/last |
    SpanTreeAtState[s] => (s.parent = so/next[s].parent)
}

// note that for the worst case topology and choice of root,
// the scope of Lvl must equal the scope of Process
run SuccessfulRun for 4 State, exactly 5 Process, 3 Lvl expect 1
// run TraceWithoutLoop for 8 but 9 State expect 1
run BadLivenessTrace for 5 but 7 State expect 0
check Closure for 5 but 7 State expect 0
