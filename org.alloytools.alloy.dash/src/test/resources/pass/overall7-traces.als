open util/ordering[Snapshot] as Snapshot
abstract sig StateLabel {}
abstract sig Root extends StateLabel {} 
one sig Root_A extends Root {} 
one sig Root_B extends Root {} 
one sig Root_C extends Root {} 
one sig Root_S1 extends Root {} 

abstract sig Identifiers {}
sig CID extends Identifiers {} 

sig Snapshot {
  scopesUsed0 : set TransitionLabel,
  conf0 : set StateLabel,
  conf1 : Identifiers -> Identifiers -> StateLabel,
  stable : one boolean/Bool
}

pred Root_S1_t1_pre[s : one Snapshot] {
  
}


pred Root_S1_t1_post[s : one Snapshot, sNext : one Snapshot] {
  sNext. (conf0) = { { s. (conf0) - Root/S1 } + Root/S1 }
  sNext. (conf1) = s. (conf1)
}

pred Root_S1_t1_semantics[s : one Snapshot, sNext : one Snapshot] {
  (stable = boolean/True => 
    sNext. (scopesUsed0) = Root_S1_t1
 else {
    sNext. (scopesUsed0) = { s. (scopesUsed0) + Root_S1_t1 } }
)
}


pred Root_S1_t1_isEnabledAfterStep[s : one Snapshot, sNext : one Snapshot, t : one TransitionLabel] {
  
}


pred Root_S1_t1[s : one Snapshot, sNext : one Snapshot] {
  s. (Root_S1_t1_pre)
  sNext. (s. (Root_S1_t1_post))
  sNext. (s. (Root_S1_t1_semantics))
}

pred Root_S1_t2_pre[s : one Snapshot] {
  
}


pred Root_S1_t2_post[s : one Snapshot, sNext : one Snapshot] {
  sNext. (conf0) = { { s. (conf0) - Root/A - Root/B - Root/S1 } + Root/A + Root/B }
  sNext. (conf1) = { { s. (conf1) - { CID -> Root/C } } + { CID -> Root/C } }
}

pred Root_S1_t2_semantics[s : one Snapshot, sNext : one Snapshot] {
  (stable = boolean/True => 
    sNext. (scopesUsed0) = Root_S1_t2
 else {
    sNext. (scopesUsed0) = { s. (scopesUsed0) + Root_S1_t2 } }
)
}


pred Root_S1_t2_isEnabledAfterStep[s : one Snapshot, sNext : one Snapshot, t : one TransitionLabel] {
  
}


pred Root_S1_t2[s : one Snapshot, sNext : one Snapshot] {
  s. (Root_S1_t2_pre)
  sNext. (s. (Root_S1_t2_post))
  sNext. (s. (Root_S1_t2_semantics))
}

pred Root_S1_t3_pre[s : one Snapshot] {
  
}


pred Root_S1_t3_post[s : one Snapshot, sNext : one Snapshot] {
  sNext. (conf0) = { { s. (conf0) - Root/A - Root/B - Root/S1 } + Root/A + Root/B }
  sNext. (conf1) = { { s. (conf1) - { CID -> Root/C } } + { { CID - c1 } -> Root/C } + { c1 -> Root/C } }
}

pred Root_S1_t3_semantics[s : one Snapshot, sNext : one Snapshot] {
  (stable = boolean/True => 
    sNext. (scopesUsed0) = Root_S1_t3
 else {
    sNext. (scopesUsed0) = { s. (scopesUsed0) + Root_S1_t3 } }
)
}


pred Root_S1_t3_isEnabledAfterStep[s : one Snapshot, sNext : one Snapshot, t : one TransitionLabel] {
  
}


pred Root_S1_t3[s : one Snapshot, sNext : one Snapshot] {
  s. (Root_S1_t3_pre)
  sNext. (s. (Root_S1_t3_post))
  sNext. (s. (Root_S1_t3_semantics))
}

pred small_step[s : one Snapshot, sNext : one Snapshot] {
  (some pCID: one CID | { sNext. (s. (Root_S1_t1)) or
    sNext. (s. (Root_S1_t2)) or
    sNext. (s. (Root_S1_t3)) })
}

