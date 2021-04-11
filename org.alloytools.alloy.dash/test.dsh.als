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
s'.concState_s.concState_var_one = s.concState_s.concState_var_one 
s'.concState_s.concState_var_one = s.concState_s.concState_var_one 
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
s'.concState_s.concState_var_one = s.concState_s.concState_var_one 
s'.concState_s.concState_var_one = s.concState_s.concState_var_one 
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
all s: Snapshot | s in initial iff init[s]
all s, s': Snapshot | s->s' in nextStep iff small_step[s, s']]
all s, s': Snapshot | equals[s, s'] => s = s'path}
}

pred path {
all s:Snapshot, s': s.next | operation[s, s']
init[first]
}

/****************************** INVARIANTS ****************************/

}
