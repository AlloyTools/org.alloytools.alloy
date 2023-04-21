open util/ordering[Snapshot] as Snapshot
abstract sig StateLabel {}
abstract sig Root extends StateLabel {} 
abstract sig Root_A extends Root {} 
one sig Root_A_S1 extends Root_A {} 
abstract sig Root_B extends Root {} 
one sig Root_B_C extends Root_B {} 
one sig Root_B_D extends Root_B {} 
abstract sig Root_B_E extends Root_B {} 
one sig Root_B_E_S2 extends Root_B_E {} 
one sig Root_B_E_S4 extends Root_B_E {} 
one sig Root_B_E_F extends Root_B_E {} 
one sig Root_B_E_G extends Root_B_E {} 
one sig Root_S3 extends Root {} 

abstract sig Identifiers {}
sig FID extends Identifiers {} 
sig EID extends Identifiers {} 
sig AID extends Identifiers {} 

sig Snapshot {
  scopesUsed0 : set TransitionLabel,
  conf0 : set StateLabel,
  conf1 : Identifiers -> Identifiers -> StateLabel,
  conf2 : Identifiers -> Identifiers -> Identifiers -> StateLabel,
  stable : one boolean/Bool
}

pred Root_t1_pre[s : one Snapshot] {
  
}


pred Root_t1_post[s : one Snapshot, sNext : one Snapshot] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { (e1 = e2 =>  e1  else { EID } ) -> Root/B/E/S2 } - { (e1 = e2 => 
    e1
 else {
    EID }
) -> Root/B/E/S4 } - { (e1 = e2 =>  e1  else { EID } ) -> Root/B/E/G } } + { { (e1 = e2 => 
    e1
 else {
    EID }
) - e2 } -> Root/B/E/S4 } + { e2 -> Root/B/E/G } }
  sNext. (conf2) = { { s. (conf2) - { FID -> (e1 = e2 =>  e1  else { EID } ) -> Root/B/E/F } } + { FID -> e2 -> Root/B/E/F } }
}

pred Root_t1_semantics[s : one Snapshot, sNext : one Snapshot] {
  (stable = boolean/True => 
    sNext. (scopesUsed0) = Root_t1
 else {
    sNext. (scopesUsed0) = { s. (scopesUsed0) + Root_t1 } }
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
  (some pFID: one FID,pEID: one EID,pAID: one AID | { sNext. (s. (Root_t1)) })
}

