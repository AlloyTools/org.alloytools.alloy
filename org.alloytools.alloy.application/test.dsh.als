sig Snapshot extends BaseSnapshot {
stable: one Bool}

/***************************** STATE SPACE *****************************/
abstract sig SystemState extends StateLabel {}
abstract sig topConcStateA extends SystemState {}
abstract sig topConcStateA_innerConcState extends topConcStateA{}
one sig topConcStateA_innerConcState_A extends topConcStateA_innerConcState{}


/***************************** TRANSITION SPACE *****************************/


/****************************** INITIAL CONDITIONS ****************************/

pred init[s: Snapshot] {s.conf = {
topConcStateA_innerConcState_A + topConcStateA + 
}
no s.taken 
no s.events & InternalEvent 
// Model Specific Constraints 
}
/***************************** MODEL DEFINITION *******************************/

pred operation[s, s': Snapshot] {
}

pred small_step[s, s': Snapshot] {
operation[s, s']
}
pred testIfNextStable[s, s': Snapshot, genEvents: set InternalEvent, t:TransitionLabel] {
}

pred isEnabled[s: Snapshot] {
}

pred equals[s, s': Snapshot] {
s'.conf = s.conf 
s'.events = s.events 
s'.taken = s.taken {
// Model specific declarations
}

fact {
all s: Snapshot | s in initial iff init[s]
all s, s': Snapshot | s->s' in nextStep iff small_step[s, s']]
all s, s': Snapshot | equals[s, s'] => s = s'
all s: Snapshot | (isEnabled[s] && no s': Snapshot | small_step[s, s']) => s.stable = False
 all s: Snapshot | s.stable = False => some s.nextStep
path}
}

pred path {
all s:Snapshot, s': s.next | operation[s, s']
init[first]
}

/****************************** INVARIANTS ****************************/

}
