sig Snapshot extends BaseSnapshot {
concState_var_one: none
}

/***************************** STATE SPACE *****************************/
abstract sig SystemState extends StateLabel {}
abstract sig concState extends SystemState {}
one sig concState_state_one extends concState{}


/***************************** TRANSITION SPACE *****************************/
one sig concState_t_1 extends TransitionLabel {}
one sig concState_trans_two extends TransitionLabel {}
one sig concState_state_one_t_2 extends TransitionLabel {}


pred pre_concState_t_1[s: Snapshot]
concState in s.conf
}

pred post_concState_t_1[s, s': Snapshot] {
s'.conf = s.conf - concState + { concState }
s.concState_var_one = none 
}

pred concState_t_1[s, s': Snapshot] {
post_concState_t_1[s, s']
pre_concState_t_1[s]
semantics_concState_t_1[s, s']
}

pred semantics_concState_t_1[s, s': Snapshot] {
s'.taken = concState_t_1
}

pred pre_concState_trans_two[s: Snapshot]
concState in s.conf
}

pred post_concState_trans_two[s, s': Snapshot] {
s'.conf = s.conf - concState + { concState }
s.concState_var_one = none 
}

pred concState_trans_two[s, s': Snapshot] {
post_concState_trans_two[s, s']
pre_concState_trans_two[s]
semantics_concState_trans_two[s, s']
}

pred semantics_concState_trans_two[s, s': Snapshot] {
s'.taken = concState_trans_two
}

pred pre_concState_state_one_t_2[s: Snapshot]
concState_state_one in s.conf
}

pred post_concState_state_one_t_2[s, s': Snapshot] {
s'.conf = s.conf - concState_state_one + { concState_state_one }
s.concState_var_one = none 
}

pred concState_state_one_t_2[s, s': Snapshot] {
post_concState_state_one_t_2[s, s']
pre_concState_state_one_t_2[s]
semantics_concState_state_one_t_2[s, s']
}

pred semantics_concState_state_one_t_2[s, s': Snapshot] {
s'.taken = concState_state_one_t_2
}

/****************************** INITIAL CONDITIONS ****************************/

pred init[s: Snapshot] {s.conf = {
concState_state_one + 
}
no s.taken 
no s.events & InternalEvent 
// Model Specific Constraints 
}
/***************************** MODEL DEFINITION *******************************/

pred operation[s, s': Snapshot] {
concState_t_1[s, s'] or 
concState_trans_two[s, s'] or 
concState_state_one_t_2[s, s'] or 
}

pred small_step[s, s': Snapshot] {
operation[s, s']
}
pred equals[s, s': Snapshot] {
s'.conf = s.conf 
s'.events = s.events 
s'.taken = s.taken {
// Model specific declarations
s'.concState_var_one = s.concState_var_one
}

fact {
all s: Snapshot | s in initial iff init[s]]
all s, s': Snapshot | s->s' in nextStep iff small_step[s, s']]
all s, s': Snapshot | equals[s, s'] => s = s'path}
}

pred path {
all s:Snapshot, s': s.next | operation[s, s']
init[first]
}

/****************************** INVARIANTS ****************************/

}
sig Snapshot extends BaseSnapshot {
concState_var_one: none
}

/***************************** STATE SPACE *****************************/
abstract sig SystemState extends StateLabel {}
abstract sig concState extends SystemState {}
one sig concState_state_one extends concState{}
one sig concState_state_two extends concState{}


/***************************** TRANSITION SPACE *****************************/
one sig concState___1 extends TransitionLabel {}
one sig concState___2 extends TransitionLabel {}


pred pre_concState___1[s: Snapshot]
concState_state_one in s.conf
concState_event_one in (s.events & EnvironmentEvent)
s.concState_s.concState_var_one = none 
s.concState_s.concState_var_one = none 
}

pred post_concState___1[s, s': Snapshot] {
s'.conf = s.conf - concState_state_one + { concState_state_one }
s'.concState_var_one = s.concState_var_one 
s'.concState_var_one = s.concState_var_one 
{concState_event_one} in s'.events
}

pred concState___1[s, s': Snapshot] {
post_concState___1[s, s']
pre_concState___1[s]
semantics_concState___1[s, s']
}

pred semantics_concState___1[s, s': Snapshot] {
s'.taken = concState___1
}

pred pre_concState___2[s: Snapshot]
concState_state_two in s.conf
concState_event_one in (s.events & EnvironmentEvent)
s.concState_s.concState_var_one = none 
s.concState_s.concState_var_one = none 
}

pred post_concState___2[s, s': Snapshot] {
s'.conf = s.conf - concState_state_two + { concState_state_one }
s'.concState_var_one = s.concState_var_one 
s'.concState_var_one = s.concState_var_one 
{concState_event_one} in s'.events
}

pred concState___2[s, s': Snapshot] {
post_concState___2[s, s']
pre_concState___2[s]
semantics_concState___2[s, s']
}

pred semantics_concState___2[s, s': Snapshot] {
s'.taken = concState___2
}

/****************************** INITIAL CONDITIONS ****************************/

pred init[s: Snapshot] {s.conf = {
concState_state_one + 
}
no s.taken 
no s.events & InternalEvent 
// Model Specific Constraints 
}
/***************************** MODEL DEFINITION *******************************/

pred operation[s, s': Snapshot] {
concState___1[s, s'] or 
concState___2[s, s'] or 
}

pred small_step[s, s': Snapshot] {
operation[s, s']
}
pred equals[s, s': Snapshot] {
s'.conf = s.conf 
s'.events = s.events 
s'.taken = s.taken {
// Model specific declarations
s'.concState_var_one = s.concState_var_one
}

fact {
all s: Snapshot | s in initial iff init[s]]
all s, s': Snapshot | s->s' in nextStep iff small_step[s, s']]
all s, s': Snapshot | equals[s, s'] => s = s'path}
}

pred path {
all s:Snapshot, s': s.next | operation[s, s']
init[first]
}

/****************************** INVARIANTS ****************************/

}
sig Snapshot extends BaseSnapshot {
stable: one BoolconcState_var_one: none -> none
concState_var_two: none -> none
innerConcState_var_three: none -> none
}

/***************************** STATE SPACE *****************************/
abstract sig SystemState extends StateLabel {}
abstract sig concState extends SystemState {}
abstract sig concState_innerConcState extends concState{}


/***************************** TRANSITION SPACE *****************************/


/****************************** INITIAL CONDITIONS ****************************/

pred init[s: Snapshot] {s.conf = {
concState + concState_innerConcState + 
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
s'.concState_var_one = s.concState_var_one
s'.concState_var_two = s.concState_var_two
s'.concState_innerConcState_var_three = s.concState_innerConcState_var_three
}

fact {
all s: Snapshot | s in initial iff init[s]]
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
sig Snapshot extends BaseSnapshot {
concState_var_one: none
}

/***************************** STATE SPACE *****************************/
abstract sig SystemState extends StateLabel {}
abstract sig concState extends SystemState {}
one sig concState_state_one extends concState{}


/***************************** TRANSITION SPACE *****************************/
one sig concState_t_1 extends TransitionLabel {}
one sig concState_trans_two extends TransitionLabel {}
one sig concState_state_one_t_2 extends TransitionLabel {}


pred pre_concState_t_1[s: Snapshot]
concState in s.conf
}

pred post_concState_t_1[s, s': Snapshot] {
s'.conf = s.conf - concState + { concState }
s.concState_var_one = none 
}

pred concState_t_1[s, s': Snapshot] {
post_concState_t_1[s, s']
pre_concState_t_1[s]
semantics_concState_t_1[s, s']
}

pred semantics_concState_t_1[s, s': Snapshot] {
s'.taken = concState_t_1
}

pred pre_concState_trans_two[s: Snapshot]
concState in s.conf
}

pred post_concState_trans_two[s, s': Snapshot] {
s'.conf = s.conf - concState + { concState }
s.concState_var_one = none 
}

pred concState_trans_two[s, s': Snapshot] {
post_concState_trans_two[s, s']
pre_concState_trans_two[s]
semantics_concState_trans_two[s, s']
}

pred semantics_concState_trans_two[s, s': Snapshot] {
s'.taken = concState_trans_two
}

pred pre_concState_state_one_t_2[s: Snapshot]
concState_state_one in s.conf
}

pred post_concState_state_one_t_2[s, s': Snapshot] {
s'.conf = s.conf - concState_state_one + { concState_state_one }
s.concState_var_one = none 
}

pred concState_state_one_t_2[s, s': Snapshot] {
post_concState_state_one_t_2[s, s']
pre_concState_state_one_t_2[s]
semantics_concState_state_one_t_2[s, s']
}

pred semantics_concState_state_one_t_2[s, s': Snapshot] {
s'.taken = concState_state_one_t_2
}

/****************************** INITIAL CONDITIONS ****************************/

pred init[s: Snapshot] {s.conf = {
concState_state_one + 
}
no s.taken 
no s.events & InternalEvent 
// Model Specific Constraints 
}
/***************************** MODEL DEFINITION *******************************/

pred operation[s, s': Snapshot] {
concState_t_1[s, s'] or 
concState_trans_two[s, s'] or 
concState_state_one_t_2[s, s'] or 
}

pred small_step[s, s': Snapshot] {
operation[s, s']
}
pred equals[s, s': Snapshot] {
s'.conf = s.conf 
s'.events = s.events 
s'.taken = s.taken {
// Model specific declarations
s'.concState_var_one = s.concState_var_one
}

fact {
all s: Snapshot | s in initial iff init[s]]
all s, s': Snapshot | s->s' in nextStep iff small_step[s, s']]
all s, s': Snapshot | equals[s, s'] => s = s'path}
}

pred path {
all s:Snapshot, s': s.next | operation[s, s']
init[first]
}

/****************************** INVARIANTS ****************************/

}
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
all s: Snapshot | s in initial iff init[s]]
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
sig Snapshot extends BaseSnapshot {
stable: one Bool}

/***************************** STATE SPACE *****************************/
abstract sig SystemState extends StateLabel {}
abstract sig topConcStateA extends SystemState {}
abstract sig topConcStateA_innerConcState extends topConcStateA{}
one sig topConcStateA_innerConcState_A extends topConcStateA_innerConcState{}
abstract sig topConcStateB extends SystemState {}
one sig topConcStateB_B extends topConcStateB{}


/***************************** TRANSITION SPACE *****************************/


/****************************** INITIAL CONDITIONS ****************************/

pred init[s: Snapshot] {s.conf = {
topConcStateA_innerConcState_A + topConcStateB_B + topConcStateA + 
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
all s: Snapshot | s in initial iff init[s]]
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
sig Snapshot extends BaseSnapshot {
}

/***************************** STATE SPACE *****************************/
abstract sig SystemState extends StateLabel {}
abstract sig topConcStateA extends SystemState {}
one sig topConcStateA_B extends topConcStateA{}


/***************************** TRANSITION SPACE *****************************/
one sig topConcStateA_A extends TransitionLabel {}
one sig topConcStateA_B_B extends TransitionLabel {}


pred pre_topConcStateA_A[s: Snapshot]
topConcStateA in s.conf
topConcStateA_A in (s.events & EnvironmentEvent)
}

pred post_topConcStateA_A[s, s': Snapshot] {
s'.conf = s.conf - topConcStateA + { topConcStateA_B }
}

pred topConcStateA_A[s, s': Snapshot] {
post_topConcStateA_A[s, s']
pre_topConcStateA_A[s]
semantics_topConcStateA_A[s, s']
}

pred semantics_topConcStateA_A[s, s': Snapshot] {
s'.taken = topConcStateA_A
}

pred pre_topConcStateA_B_B[s: Snapshot]
topConcStateA_B in s.conf
topConcStateA_A in (s.events & EnvironmentEvent)
}

pred post_topConcStateA_B_B[s, s': Snapshot] {
s'.conf = s.conf - topConcStateA_B + { topConcStateA_B }
}

pred topConcStateA_B_B[s, s': Snapshot] {
post_topConcStateA_B_B[s, s']
pre_topConcStateA_B_B[s]
semantics_topConcStateA_B_B[s, s']
}

pred semantics_topConcStateA_B_B[s, s': Snapshot] {
s'.taken = topConcStateA_B_B
}

/****************************** INITIAL CONDITIONS ****************************/

pred init[s: Snapshot] {s.conf = {
topConcStateA_B + 
}
no s.taken 
no s.events & InternalEvent 
// Model Specific Constraints 
}
/***************************** MODEL DEFINITION *******************************/

pred operation[s, s': Snapshot] {
topConcStateA_A[s, s'] or 
topConcStateA_B_B[s, s'] or 
}

pred small_step[s, s': Snapshot] {
operation[s, s']
}
pred equals[s, s': Snapshot] {
s'.conf = s.conf 
s'.events = s.events 
s'.taken = s.taken {
// Model specific declarations
}

fact {
all s: Snapshot | s in initial iff init[s]]
all s, s': Snapshot | s->s' in nextStep iff small_step[s, s']]
all s, s': Snapshot | equals[s, s'] => s = s'path}
}

pred path {
all s:Snapshot, s': s.next | operation[s, s']
init[first]
}

/****************************** INVARIANTS ****************************/

}
sig Snapshot extends BaseSnapshot {
}

/***************************** STATE SPACE *****************************/
abstract sig SystemState extends StateLabel {}
abstract sig concState extends SystemState {}
one sig concState_topStateA extends concState{}
one sig concState_topStateB extends concState{}


/***************************** TRANSITION SPACE *****************************/


/****************************** INITIAL CONDITIONS ****************************/

pred init[s: Snapshot] {s.conf = {
concState_topStateA + concState_topStateA_innerState + 
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
pred equals[s, s': Snapshot] {
s'.conf = s.conf 
s'.events = s.events 
s'.taken = s.taken {
// Model specific declarations
}

fact {
all s: Snapshot | s in initial iff init[s]]
all s, s': Snapshot | s->s' in nextStep iff small_step[s, s']]
all s, s': Snapshot | equals[s, s'] => s = s'path}
}

pred path {
all s:Snapshot, s': s.next | operation[s, s']
init[first]
}

/****************************** INVARIANTS ****************************/

}
sig Snapshot extends BaseSnapshot {
concState_var_one: none
}

/***************************** STATE SPACE *****************************/
abstract sig SystemState extends StateLabel {}
abstract sig concState extends SystemState {}
one sig concState_state_one extends concState{}
one sig concState_state_two extends concState{}


/***************************** TRANSITION SPACE *****************************/
one sig concState_t_1 extends TransitionLabel {}
one sig concState_t_2 extends TransitionLabel {}


pred pre_concState_t_1[s: Snapshot]
concState_state_one in s.conf
concState_event_one in (s.events & EnvironmentEvent)
s.concState_s.concState_var_one = none 
s.concState_s.concState_var_one = none 
}

pred post_concState_t_1[s, s': Snapshot] {
s'.conf = s.conf - concState_state_one + { concState_state_two }
s'.concState_var_one = s.concState_var_one 
s'.concState_var_one = s.concState_var_one 
{concState_event_one} in s'.events
}

pred concState_t_1[s, s': Snapshot] {
post_concState_t_1[s, s']
pre_concState_t_1[s]
semantics_concState_t_1[s, s']
}

pred semantics_concState_t_1[s, s': Snapshot] {
s'.taken = concState_t_1
}

pred pre_concState_t_2[s: Snapshot]
concState_state_two in s.conf
concState_event_one in (s.events & EnvironmentEvent)
s.concState_s.concState_var_one = none 
s.concState_s.concState_var_one = none 
}

pred post_concState_t_2[s, s': Snapshot] {
s'.conf = s.conf - concState_state_two + { concState_state_two }
s'.concState_var_one = s.concState_var_one 
s'.concState_var_one = s.concState_var_one 
{concState_event_one} in s'.events
}

pred concState_t_2[s, s': Snapshot] {
post_concState_t_2[s, s']
pre_concState_t_2[s]
semantics_concState_t_2[s, s']
}

pred semantics_concState_t_2[s, s': Snapshot] {
s'.taken = concState_t_2
}

/****************************** INITIAL CONDITIONS ****************************/

pred init[s: Snapshot] {s.conf = {
concState_state_one + 
}
no s.taken 
no s.events & InternalEvent 
// Model Specific Constraints 
}
/***************************** MODEL DEFINITION *******************************/

pred operation[s, s': Snapshot] {
concState_t_1[s, s'] or 
concState_t_2[s, s'] or 
}

pred small_step[s, s': Snapshot] {
operation[s, s']
}
pred equals[s, s': Snapshot] {
s'.conf = s.conf 
s'.events = s.events 
s'.taken = s.taken {
// Model specific declarations
s'.concState_var_one = s.concState_var_one
}

fact {
all s: Snapshot | s in initial iff init[s]]
all s, s': Snapshot | s->s' in nextStep iff small_step[s, s']]
all s, s': Snapshot | equals[s, s'] => s = s'path}
}

pred path {
all s:Snapshot, s': s.next | operation[s, s']
init[first]
}

/****************************** INVARIANTS ****************************/

}
