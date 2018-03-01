module examples/algorithms/stable_mutex_ring

/*
 * Dijkstra's K-state mutual exclusion algorithm for a ring
 *
 * Original paper describing the algorithm:
 *   [1] E.W.Dijkstra, "Self-Stabilizing Systems in Spite of
 *   Distributed Control", Comm. ACM, vol. 17, no. 11, pp.
 *   643-644, Nov. 1974
 *
 * Proof of algorithm's correctness:
 *   [2] E.W.Dijkstra, "A Belated Proof of Self-Stabilization",
 *   in Distributed Computing, vol. 1, no. 1, pp. 5-6, 1986
 *
 * SMV analysis of this algorithm is described in:
 *   [3] "Symbolic Model Checking for Self-Stabilizing Algorithms",
 *   by Tatsuhiro Tsuchiya, Shini'ichi Nagano, Rohayu Bt Paidi, and
 *   Tohru Kikuno, in IEEE Transactions on Parallel and Distributed
 *   Systems, vol. 12, no. 1, January 2001
 *
 * Description of algorithm (adapted from [3]):
 *
 * Consider a distributed system that consists of n processes
 * connected in the form of a ring.  We assume the state-reading
 * model in which processes can directly read the state of their
 * neighbors.  We define _privilege_ of a process as its ability to
 * change its current state.  This ability is based on a Boolean
 * predicate that consists of its current state and the state of
 * one of its neighboring processes.
 *
 * We then define the legitimate states as those in which the
 * following two properties hold: 1) exactly one process has a
 * privilege, and 2) every process will eventually have a privilege.
 * These properties correspond to a form of mutual exclusion, because
 * the privileged process can be regarded as the only process that is
 * allowed in its critical section.
 *
 * In the K-state algorithm, the state of each process is in
 * {0,1,2,...,K-1}, where K is an integer larger than or equal to n.
 * For any process p_i, we use the symbols S and L to denote its
 * state and the state of its neighbor p_{i-1}, respectively, and
 * process p_0 is treated differently from all other processes. The
 * K-state algorithm is described below.
 *
 *   process p_0: if (L=S) { S := (S+1) mod K; }
 *   process P_i(i=1,...,n-1): if (L!=S) { S:=L; }
 */

open util/ordering[Tick] as to
open util/graph[Process] as pg
open util/graph[Val] as vg

sig Process {
  rightNeighbor: Process
}

sig Val {
  nextVal : Val
}

fact MoreValThanProcess {
  # Val > # Process
}

fact DefineRings {
  pg/ring[rightNeighbor]
  vg/ring[nextVal]
  //Val$nextVal = Ord[Val].next + (Ord[Val].last -> Ord[Val].first)
}

sig Tick {
  val: Process -> one Val,
  runs: set Process,    // processes scheduled to run on this tick
  // for visualization
  priv: set Process  // the set of priviledged processes on this tick
}
{
  priv = { p : Process | Privileged[p, this] }
}

one sig FirstProc extends Process {
}


fun FirstProcTrans[curVal, neighborVal : Val]: Val {
  (curVal = neighborVal) => curVal.nextVal else curVal
}

fun RestProcTrans[curVal, neighborVal : Val]: Val {
  (curVal != neighborVal) => neighborVal else curVal
}

fact LegalTrans {
  all tp : Tick - to/last |
    let tn = to/next[tp] | {
        all p: Process |
           let curVal = tp.val[p], neighborVal = tp.val[p.rightNeighbor], newVal = tn.val[p] | {
                p !in tp.runs => newVal = curVal else {
                   p = FirstProc =>
                       newVal = FirstProcTrans[curVal, neighborVal]
                   else
                       newVal = RestProcTrans[curVal, neighborVal]
                }
          }
      }
}

pred TickTrans[tp, tn : Tick] {
  all p : Process |
    let curVal = tp.val[p], neighborVal = tp.val[p.rightNeighbor], newVal = tn.val[p] | {
                   p = FirstProc =>
                       newVal = FirstProcTrans[curVal, neighborVal]
                   else
                       newVal = RestProcTrans[curVal, neighborVal]
    }
}

pred Privileged[p : Process, t : Tick] {
  // whether this process can enter its critical section
  // on this tick
  p = FirstProc =>
    t.val[p] = t.val[p.rightNeighbor]
  else
    t.val[p] != t.val[p.rightNeighbor]
}

pred IsomorphicStates[val1, val2: Process -> one Val] {
   some processMap: Process one -> one Process,
        valMap: Val one -> one Val | {
       FirstProc.processMap = FirstProc
       all p: Process, v: Val |  {
          p->v in val1 iff (p.processMap) -> (v.valMap) in val2
       }
       all v1,v2: Val | v1->v2 in nextVal iff (v1.valMap) ->  (v2.valMap) in nextVal
       all p1,p2: Process | p1->p2 in rightNeighbor
               iff (p1.processMap) ->  (p2.processMap) in rightNeighbor
   }
}

pred BadSafetyTrace {
  // Find a trace that goes into a loop
  // containing a bad tick, i.e. a tick
  // at which two distinct processes
  // try to run their critical sections
  // simultaneously.  In such a trace the
  // algorithm never "stabilizes".
  let lst = to/last |
    some t : Tick - lst | {
      //IsomorphicStates(ft.val, lst.val)
      t.val = lst.val
      Process in (to/nexts[t] + t - lst).runs
      some badTick : to/nexts[t] + t |
        BadTick[badTick]
    }
}

pred BadTick[badTick : Tick] {
      // Two different processes simultaneously
      // try to run their critical sections at this tick
      some p1 , p2 : Process | {
        p1!=p2
        Privileged[p1, badTick]
        Privileged[p2, badTick]
      }
}

assert Closure {
  not BadTick[to/first] => (all t : Tick | not BadTick[t])
}

pred TwoPrivileged {
  BadTick[to/first]
  some p1, p2 : Process, t1, t2 : Tick - to/first | {
    p1!=p2
    Privileged[p1,t1]
    Privileged[p2,t2]
  }
}

pred TraceWithoutLoop  {
  all t1, t2 : Tick | t1!=t2 => t1.val != t2.val
}

pred TraceShorterThanMaxSimpleLoop {
  to/first.val = to/last.val
  all t : Tick - to/first - to/last |
    !(t.val = to/first.val)
}

run TraceShorterThanMaxSimpleLoop for 7 but 2 Process, 3 Val expect 1
run TwoPrivileged for 5 but 3 Process, 4 Val expect 1
check Closure for 5 but 5 Process, 6 Val expect 0
//run BadSafetyTrace for 16 but 3 Process, 4 Val
//run TraceWithoutLoop for 21 but 4 Process, 5 Val


