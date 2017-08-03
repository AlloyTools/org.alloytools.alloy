module examples/algorithms/stable_orient_ring

/*
 * A self-stabilizing algorithm for orienting uniform rings.
 * Communication model is the state-reading model.
 */

open util/boolean as bool
open util/ordering[Tick] as ord
open util/graph[Process] as graph

sig Process {
  rightNeighbor: Process,
  AP1, AP2: Process
}

fun leftNeighbor[p: Process]: Process {
  p.~(rightNeighbor)
}

fact {
  all p: Process {
     (p.AP1=p.rightNeighbor && p.AP2=leftNeighbor[p]) ||
     (p.AP2=p.rightNeighbor && p.AP1=leftNeighbor[p])
  }
}

fact DefineRing {
  graph/ring[rightNeighbor]
}

sig Tick {
  runs: set Process,
  dir, S, T: Process -> one Bool,
  ring_: Process -> Process
}
{
  all p: Process | p.ring_ = (p.dir=True => p.AP1 else p.AP2)
}

pred Eq3[b1,b2,b3: Bool] { b1 = b2 && b2 = b3 }
pred Eq4[b1,b2,b3,b4: Bool] { Eq3[b1,b2,b3] && b3=b4 }

fact  Transitions {
   all tp: Tick - ord/last | let tn = ord/next[tp] |
       all p: Process |
        let p1 = p.AP1, p2 = p.AP2, pS = tp.S, pT=tp.T, nS=tn.S, nT=tn.T |
           let S1p=p1.pS, S2p=p2.pS,
               T1p=p1.pT, T2p=p2.pT,
               Sp = p.pS, Sn=p.nS,
               Tp = p.pT, Tn=p.nT,
               dirp = p.(tp.dir), dirn = p.(tn.dir) | {
           p !in tp.runs => ( Sn = Sp && Tn = Tp && dirn = dirp ) else (
           S1p = S2p => ( Sn = Not[S1p] && Tn = True && dirn=dirp) else (
             (Eq3[S1p, Sp, Not[S2p]] &&
              Eq4[Not[T1p],Tp,T2p,True]) =>
                (Sn = Not[Sp] && Tn = False && dirn = True)
              else (
                 (Eq3[Not[S1p],Sp,S2p] && Eq4[T1p,Tp,Not[T2p],True]) =>
                 (Sn = Not[Sp] && Tn = False && dirn = False) else (
                    ((Eq3[S1p,Sp,Not[S2p]] && T1p=Tp) ||
                    (Eq3[Not[S1p],Sp,S2p] && Tp=T2p)) =>
                    (Tn = Not[Tp] && Sn=Sp && dirn=dirp) else (
                       Sn=Sp && Tn=Tp && dirn=dirp
                    )
                 )
              )
           )
         )
       }
}

pred RingAtTick[t: Tick] {
   let rng = t.ring_ |
      graph/ring[rng] || graph/ring[~rng]
}

assert Closure {
   // if the ring is properly oriented
   all t: Tick - ord/last |
      RingAtTick[t] => RingAtTick[ord/next[t]]
}

pred SomeState  {
   !graph/ring[ord/first.ring_]
   some t: Tick | graph/ring[t.ring_]
}

run SomeState for 1 but 2 Tick, 2 Bool, 3 Process expect 1
check Closure for 1 but 2 Tick, 2 Bool, 3 Process expect 1
