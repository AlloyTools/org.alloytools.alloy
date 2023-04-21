open util/ordering[Snapshot] as Snapshot
abstract sig StateLabel {}
abstract sig Root extends StateLabel {} 
abstract sig Root_A extends Root {} 
abstract sig Root_A_B extends Root_A {} 
one sig Root_A_B_S1 extends Root_A_B {} 
abstract sig Root_C extends Root {} 
one sig Root_C_S2 extends Root_C {} 

abstract sig TransitionLabel {}
one sig Root_t1 extends TransitionLabel {} 

abstract sig Identifiers {}
sig AID extends Identifiers {} 
sig BID extends Identifiers {} 
sig CID extends Identifiers {} 

sig Snapshot {
  taken0 : set TransitionLabel,
  conf0 : set StateLabel,
  conf1 : Identifiers -> StateLabel,
  conf2 : Identifiers -> Identifiers -> StateLabel,
  stable : one boolean/Bool
}

pred Root_t1_pre[s : one Snapshot] {
  
}


pred Root_t1_post[s : one Snapshot, sNext : one Snapshot] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - Root/C/S2 } + Root/C/S2 + Root/C/S2 }
  sNext. (conf2) = { { s. (conf2) - { AID -> Root/A/B/S1 } } + { AID -> Root/A/B/S1 } }
}

pred Root_t1_semantics[s : one Snapshot, sNext : one Snapshot] {
  (stable = boolean/True => 
    sNext. (taken0) = Root_t1
 else {
    sNext. (taken0) = { s. (taken0) + Root_t1 } }
)
}


pred Root_t1_isEnabledAfterStep[s : one Snapshot, sNext : one Snapshot, t : one TransitionLabel] {
  
}


pred Root_t1[s : one Snapshot, sNext : one Snapshot] {
  s. (Root_t1_pre)
  sNext. (s. (Root_t1_post))
  sNext. (s. (Root_t1_semantics))
}

pred small_step[s : one Snapshot, sNext : one Snapshot] {
  (some pAID: one AID,pBID: one BID,pCID: one CID | { sNext. (s. (Root_t1)) })
}

