open util/ordering[Snapshot] as Snapshot
abstract sig StateLabel {}
sig Root extends StateLabel {} 
abstract sig Root_S1 extends Root {} 
sig Root_S1_S7 extends Root_S1 {} 
abstract sig Root_S2 extends Root {} 
abstract sig Root_S2_S3 extends Root_S2 {} 
abstract sig Root_S2_S3_S4 extends Root_S2_S3 {} 

abstract sig TransitionLabel {}
one sig Root_S1_t1 extends TransitionLabel {} 
one sig Root_S2_S3_S4_t2 extends TransitionLabel {} 

sig Snapshot {
  taken0 : set TransitionLabel,
  conf0 : set StateLabel,
  stable : one boolean/Bool
}

pred Root_S1_t1_pre[s : one Snapshot] {
  
}


pred Root_S1_t1_post[s : one Snapshot, sNext : one Snapshot] {
  
}

pred Root_S1_t1_semantics[s : one Snapshot, sNext : one Snapshot] {
  (stable = boolean/True => 
    sNext. (taken0) = Root_S1_t1
 else {
    sNext. (taken0) = { s. (taken0) + Root_S1_t1 } }
)
}


pred Root_S1_t1_isEnabledAfterStep[s : one Snapshot, sNext : one Snapshot, t : one TransitionLabel] {
  
}


pred Root_S1_t1[s : one Snapshot, sNext : one Snapshot] {
  s. (Root_S1_t1_pre)
  sNext. (s. (Root_S1_t1_post))
  sNext. (s. (Root_S1_t1_semantics))
}

pred Root_S2_S3_S4_t2_pre[s : one Snapshot] {
  
}


pred Root_S2_S3_S4_t2_post[s : one Snapshot, sNext : one Snapshot] {
  
}

pred Root_S2_S3_S4_t2_semantics[s : one Snapshot, sNext : one Snapshot] {
  (stable = boolean/True => 
    sNext. (taken0) = Root_S2_S3_S4_t2
 else {
    sNext. (taken0) = { s. (taken0) + Root_S2_S3_S4_t2 } }
)
}


pred Root_S2_S3_S4_t2_isEnabledAfterStep[s : one Snapshot, sNext : one Snapshot, t : one TransitionLabel] {
  
}


pred Root_S2_S3_S4_t2[s : one Snapshot, sNext : one Snapshot] {
  s. (Root_S2_S3_S4_t2_pre)
  sNext. (s. (Root_S2_S3_S4_t2_post))
  sNext. (s. (Root_S2_S3_S4_t2_semantics))
}

pred small_step[s : one Snapshot, sNext : one Snapshot] {
  { sNext. (s. (Root_S1_t1)) or sNext. (s. (Root_S2_S3_S4_t2)) }
}

