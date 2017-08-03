module examples/algorithms/peterson

/*
 * Model of Peterson's algorithm for mutual exclusion of n
 * processes. The names kept similar to Murphi specification
 * to make correspondence clear.
 */

open util/ordering[priority] as po
open util/ordering[State] as so

sig pid {
}

sig priority {
}

fact {
  # priority = # pid + 1
}

abstract sig label_t {}

// here subtyping would help
one sig L0, L1, L2, L3, L4 extends label_t {}

sig State {
  P: pid -> label_t,
  Q: pid -> priority,
  turn: priority -> pid,
  localj: pid -> priority
}

pred NOPTrans[i: pid, pre, post : State] {
  post.P[i] = pre.P[i]
  post.Q[i] = pre.Q[i]
  post.localj[i] = pre.localj[i]
}

pred L0TransPre[i : pid, pre : State] {
  // precondition
  pre.P[i] = L0
}

pred L0Trans[i: pid, pre, post : State] {
  L0TransPre[i, pre]
  // localj[i] := 1
  post.localj[i] = po/next[po/first]
  post.P[i] = L1
  post.Q[i] = pre.Q[i]
  // something for turn?
  post.turn = pre.turn
}

pred L1TransPre[i : pid, pre : State] {
  // precondition
  pre.P[i] = L1
}

pred L1Trans[i : pid, pre, post : State] {
  L1TransPre[i, pre]
  post.localj[i] = pre.localj[i]
  post.Q[i] = pre.localj[i]
  post.P[i] = L2
  // something for turn?
  post.turn = pre.turn
}

pred L2TransPre[i : pid, pre : State] {
  // precondition
  pre.P[i] = L2
}

pred L2Trans[i : pid, pre, post : State] {
  L2TransPre[i, pre]
  post.localj[i] = pre.localj[i]
  post.Q[i] = pre.Q[i]
  post.P[i] = L3
  post.turn[post.localj[i]] = i
  all j : priority - post.localj[i] |
    post.turn[j] = pre.turn[j]
}

pred L3TransPre[i : pid, pre : State] {
  // precondition
  pre.P[i] = L3

  all k : pid - i |
    po/lt[pre.Q[k], pre.localj[i]] ||
    pre.turn[pre.localj[i]] != i
}

pred L3Trans[i : pid, pre, post : State] {
  L3TransPre[i, pre]
    post.localj[i] = po/next[pre.localj[i]]
    po/lt[post.localj[i], po/last] =>
      post.P[i] = L1
    else
      post.P[i] = L4
    post.Q[i] = pre.Q[i]
    post.turn = pre.turn
}

pred L4TransPre[i : pid, pre : State] {
  // precondition
  pre.P[i] = L4
}

pred L4Trans[i : pid, pre, post : State] {
  L4TransPre[i, pre]

  post.P[i] = L0
  post.Q[i] = po/first
  post.localj[i] = pre.localj[i]
  post.turn = pre.turn
}

pred RealTrans[i : pid, pre, post : State] {
  L0Trans[i,pre,post] ||
  L1Trans[i,pre,post] ||
  L2Trans[i,pre,post] ||
  L3Trans[i,pre,post] ||
  L4Trans[i,pre,post]
}

pred SomePre[i : pid, pre : State] {
  L0TransPre[i, pre] ||
  L1TransPre[i, pre] ||
  L2TransPre[i, pre] ||
  L3TransPre[i, pre] ||
  L4TransPre[i, pre]
}

fact Init {
  let firstState = so/first | {
    all i : pid | {
      firstState.P[i] = L0
      firstState.Q[i] = po/first
    }
    no firstState.turn
    no firstState.localj
  }
}

fact LegalTrans {
  all pre : State - so/last |
    let post = so/next[pre] | {
      /*some i : pid | {
        // HACK:
        // need to specify that if some node
        // can make a non-NOP transition, it
        // does, but i can't figure out how
        // right now
        Trans(i,pre,post) && !NOPTrans(i,pre,post)
        all j : pid - i |
          NOPTrans(j,pre,post)
      }*/
      all i : pid |
        RealTrans[i,pre,post] || NOPTrans[i,pre,post]
      (all i : pid | NOPTrans[i,pre,post]) => {
         all i : pid | !SomePre[i,pre]
         post.turn = pre.turn
      }
    }
}

assert Safety {
  all i1, i2 : pid, s : State | i1!=i2 =>  not (s.P[i1] = L4 && s.P[i2] = L4)
}

assert NotStuck {
  all pre : State - so/last |
    let post = so/next[pre] |
      some i : pid |
        RealTrans[i, pre, post] && !NOPTrans[i,pre,post]
}

pred TwoRun {
  some s1, s2: State, i1, i2: pid | {
    s1!=s2
    i1!=i2
    s1.P[i1] = L4
    s2.P[i2] = L4
  }
}

pred ThreeRun  {
  some disj s1, s2, s3: State, disj i1, i2, i3: pid | {
    s1.P[i1] = L4
    s2.P[i2] = L4
    s3.P[i3] = L4
  }
}

// 2 pids requires 8 states
// 3 pids requires 16 states
run TwoRun for 13 but 3 pid, 4 priority, 5 label_t expect 1

// haven't run this one successfully yet
run ThreeRun for 19 but 3 pid,4 priority,5 label_t expect 1

// how many states do we need for this to match murphi?
check Safety for 10 but 2 pid, 3 priority, 5 label_t expect 0

// this assertion is trivial because of the hack described above
check NotStuck for 10 but 2 pid, 3 priority, 5 label_t expect 0
