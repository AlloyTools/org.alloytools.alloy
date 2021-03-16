/*******************************************************************************
 * Title: steps.als
 * Authors: Jose Serna - jserna@uwaterloo.ca
 *
 * Notes: This module helps defining step relations for transition systems.
 *        Several axioms are included to get a significant model.
 *
 ******************************************************************************/

module steps[S]

open ctl[S]

    one sig Step {
        initial: some S,
        next_step: S -> S,
        equality:  S -> S
    }

    // A snapshot is a set of control states, a variable evaluation, and a set
    // of events.
    abstract sig BaseSnapshot {
        /** Label control states */
        conf: set StateLabel,
        /** Semantics consistency */
        taken: set TransitionLabel
    }

    fact {
        all s: S | s in BaseSnapshot
        Step.next_step = nextState
        Step.initial = initialState
    }

    // These functions must be defined by the calling code
    /** Define the elements that represent the initial state of the system */
    fun initial: S { Step.initial }
    /** Define the next state relation */
    fun nextStep: S -> S { Step.next_step }
    /** Define the criteria to consider two elements as equal */
    fun equals: S->S { Step.equality }

/****************************** EVENT SPACE ***********************************/
    abstract sig EventLabel {}
    abstract sig EnvironmentEvent, InternalEvent extends EventLabel {}

/****************************** STATE SPACE ***********************************/
    abstract sig StateLabel {}

/***************************** TRANSITIONS ************************************/
    abstract sig TransitionLabel {}

/************************* Significance Axioms ********************************/

    pred reachabilityAxiom {
        all s : S | s in S .((Step.initial) <: * (Step.next_step) )
    }

    pred equalityAxiom {
        all s, s': S |  s->s' in Step.equality => s = s'
    }

    // The system is always in some state
    assert check_some_conf {
        ctl_mc[ag[{s: S | some s.conf}]]
    }
    check check_some_conf for 10 expect 0
