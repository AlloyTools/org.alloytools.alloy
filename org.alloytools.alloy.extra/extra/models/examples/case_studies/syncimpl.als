module examples/case_studies/syncimpl

/*
 * Model of a file synchronizer reconciliation algorithm.
 *
 * Adapted from:
 *   Reference: S. Balasubramaniam and Benjamin C. Pierce,
 *   "What is a File Synchronizer", Indiana University CSCI
 *   Technical Report #507, April 22, 1998
 *
 * For a detailed description, see:
 *   http://sdg.lcs.mit.edu/pubs/theses/tnolte_masters.pdf
 *
 * author: Tina Nolte
 */

open examples/case_studies/sync as sync
open util/ordering[sync/Name] as ord
open util/relation as rel

// Model the reconciliation algorithm

sig ReconName extends Name {
   Ain, Bin, Aout, Bout: Name->FileContents,
   p_children: set Name,
   first_p_child, last_p_child: lone Name,
   prev_p_child: (p_children - first_p_child) -> p_children
}

fact {
  all x: ReconName {
     x.p_children = ChildrenAB[x.Ain, x.Bin, x]
     x.first_p_child = { pc: x.p_children | x.p_children in (pc + nexts[pc]) }
     x.last_p_child = { pc: x.p_children | x.p_children in (pc + prevs[pc]) }
     all p_child: x.p_children - x.first_p_child | {
       let earlierChildren = prevs[p_child] & x.p_children |
          p_child . (x.prev_p_child) = { earlierChild: earlierChildren | earlierChildren in (earlierChild + @prevs[earlierChild]) }
     }
  }
}

fact { ReconName = Name }

fun ChildrenAB[A, B: Name -> lone FileContents, p: Name]: set Name {
   p.children & (dom[A] + dom[B])
}

pred reconHelper[Adirty, Bdirty: set Name] {
   all p: Name {
      let A = p.Ain, B = p.Bin, A' = p.Aout, B' = p.Bout | {
         some p.(A+B) => {
             (p !in Adirty && p !in Bdirty) => (A' = A  && B' = B)  else {
             (p.A = Dir && p.B = Dir) => {
                no p_children => {
                  p.Aout = p.Ain
                  p.Bout = p.Bin
                } else {
                    p.first_p_child.Ain = p.Ain
                    p.first_p_child.Bin = p.Bin
                    p.Aout = p.last_p_child.Aout
                    p.Bout = p.last_p_child.Bout
                    all pchild: p.p_children - p.first_p_child | {
                        pchild.Ain = (pchild.(p.prev_p_child)).Aout
                        pchild.Bin = (pchild.(p.prev_p_child)).Bout
                     }
                }  // some p_children
             } else {  // !(p.A = Dir && p.B = Dir)
               p !in Adirty => {
                 A' = RestrictFS[B, p] + RestrictFSComplement[A, p]
                 B' = B
               } else {
                  p !in Bdirty => {
                     A' = A
                     B' = RestrictFS[A, p] + RestrictFSComplement[B, p]
                  } else {
                     A' = A
                     B' = B
                  }
               }  // not "p !in Adirty"
             }  // not case 2 i.e. not both are dirs
          }  // not both clean
       }  // some p.(A+B)
      }  // let A =, B=, A'=, B'=
    } // all p: Name
}  // reconHelper()

pred recon[A, B, A', B': Name -> lone FileContents, Adirty, Bdirty: set Name] {
   A = ReconName.Ain
   B = ReconName.Bin
   A' = ReconName.Aout
   B' = ReconName.Bout
   reconHelper[Adirty, Bdirty]
}

assert Correctness {
  all A, B, A', B': Name -> lone FileContents, Adirty, Bdirty: set Name | {
    {
     DirtiesValid[A, B, Adirty, Bdirty]
     recon[A, B, A', B', Adirty, Bdirty]
     //no Adirty + Bdirty
    }
    =>
     SyncSpec[A, B, A', B', Adirty, Bdirty]
  }
}

check Correctness for 4 but 2 FileContents expect 0
