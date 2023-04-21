open util/ordering[Snapshot] as Snapshot
abstract sig StateLabel {}
sig Root extends StateLabel {} 
one sig Root_A extends Root {} 
one sig Root_A_B extends Root_A {} 
one sig Root_A_B_S1 extends Root_A_B {} 
one sig Root_A_S2 extends Root_A {} 

abstract sig Identifiers {}
sig AID extends Identifiers {} 
sig BID extends Identifiers {} 

sig Snapshot {
  scopesUsed0 : set StateLabel,
  conf0 : set StateLabel,
  scopesUsed1 : Identifiers -> Identifiers -> StateLabel,
  conf1 : Identifiers -> Identifiers -> StateLabel,
  scopesUsed2 : Identifiers -> Identifiers -> Identifiers -> StateLabel,
  conf2 : Identifiers -> Identifiers -> Identifiers -> StateLabel,
  stable : one boolean/Bool
}

pred Root_A_B_S1_t1_pre[s : one Snapshot, pAID : one AID, pBID : one BID] {
  { b1 -> a1 -> Root/A/B/S1 } in s. (conf2)
  ! {Root in scopesUsed0}
  ! {{ (a1 = a2 =>  a1  else { AID } ) -> Root/A } in scopesUsed1}
}


pred Root_A_B_S1_t1_post[s : one Snapshot, sNext : one Snapshot, pAID : one AID, pBID : one BID] {
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { { s. (conf1) - { (a1 = a2 =>  a1  else { AID } ) -> Root/A/S2 } } + { a2 -> Root/A/S2 } }
  sNext. (conf2) = { { s. (conf2) - { BID -> (a1 = a2 =>  a1  else { AID } ) -> Root/A/B/S1 } } + { BID -> { (a1 = a2 => 
    a1
 else {
    AID }
) - a2 } -> Root/A/B/S1 } }
  sNext. (conf0) = s. (conf0)
  sNext. (conf1) = { s. (conf1) + { (a1 = a2 =>  a1  else { AID } ) -> Root/A } }
  sNext. (conf2) = s. (conf2)
}

pred Root_A_B_S1_t1_semantics[s : one Snapshot, sNext : one Snapshot, pAID : one AID, pBID : one BID] {
  (stable = boolean/True => 
    sNext. (scopesUsed2) = { BID -> AID -> Root_A_B_S1_t1 }
 else {
    sNext. (scopesUsed2) = { s. (scopesUsed2) + { AID -> BID -> Root_A_B_S1_t1 } } }
)
}


pred Root_A_B_S1_t1_isEnabledAfterStep[s : one Snapshot, sNext : one Snapshot, pAID : one AID, pBID : one BID, t : one TransitionLabel] {
  
}


pred Root_A_B_S1_t1[s : one Snapshot, sNext : one Snapshot, pAID : one AID, pBID : one BID] {
  pBID. (pAID. (s. (Root_A_B_S1_t1_pre)))
  pBID. (pAID. (sNext. (s. (Root_A_B_S1_t1_post))))
  pBID. (pAID. (sNext. (s. (Root_A_B_S1_t1_semantics))))
}

pred small_step[s : one Snapshot, sNext : one Snapshot] {
  (some pAID: one AID,pBID: one BID | { pBID. (pAID. (sNext. (s. (Root_A_B_S1_t1)))) })
}

