module tests/test --- example written by M.Au. Fortes da Cruz - EYLIM

-- Alloy version 3.0  - Author: M.Au. Fortes da Cruz - EYLIM
--________________________________________________________
//  SPECIFCATIONS OF CONCEPTUAL MODELS
//Purpose: Assess the correctness of the AMBERS CoDM structure
// For further conceptual model integrity analyses ...
// File concepts_State_Sim_v1.als simulate AMBERS concepts states.
--________________________________________________________
--_______________FILES____________________________________
-- models/work/ambers/concepts/concepts_Ops_Sim_Test_Assn_v1

open util/ordering[Boundary] as UB          -- introduces ordered Boundaries


// Abstract classifiers as abstract signatures:

abstract sig Transform{
    entry: set Kind,    -- an entry relates to any number of kinds
    exit:   set Kind,   -- an exit relates to any number of kinds
    body: set Function  -- a body relates to any number of functions
}{
    no entry &  exit
    #entry>1                -- Non empty set of entries
    #exit >1                -- Non empty set of exits
    #body>0             -- a Transform body  has at least 1 Function
}

abstract sig Function{
    entry: set Kind,    -- an entry relates to any number of kinds
    exit:   one Kind,   -- an exit relates to exactly one kind
    body:  lone Role    -- a body relates to at most one role.
}{
    no entry &  exit
    #entry>1                -- Non empty set of entries
    #exit >1                -- Non empty set of exits
    #body>0             -- a Function body  has at least 1 Role
}

abstract sig Kind{
    feature:        set Attribute,      -- relates to any number  of  attributes
    defcon:     set Definition_Condition    -- Constraints on Kinds
}{
    #feature>1
    #defcon>0
}

abstract sig Role{
    operation:  set Behaviour,          -- relates to 0 or N behaviour only
    hdgcon: set Handling_Condition  -- Constraints on Roles
}{
    #operation>0
    #hdgcon>0
}

abstract sig Port{
}

abstract sig Type{
}



--________________________________________________________
// Partitioning functions
sig Attribute extends Kind{
    var, par:               Type one -> one State   -- relate 1 type to 1 state
--  glb, min, max, lub:     one Boundary                -- relates to 1 limit
} {
    var != par                      -- Variables and Parameters are distinct
--  lte(glb, min)                   -- Greater Lower Bound =< Min
--  lte(min, max)                   -- Min =< Max
--  lte(max, glb)                   -- Max =< Lower Upper Bound
}

sig Behaviour extends Role{
    body:   set State -> one State      -- relates any number of states to 1 state
}

sig Discrete extends Port{      -- Discrete relates to any number of field-type
--  signal: Boolean         -- Event driving or driven/ reactive
}
sig Analog extends Port{        -- Analog relates to any number of field-type
--  dataB:   Boolean,           -- State driving or driven as controlled data
--  dataI:  Integer,
--  dataR:  Real,
--  dataC:  Character,
--  dataS:  String
}

sig Hybrid extends Port{        -- Hybrid relates to any number of field-relations
    hyb:    (Discrete -> Analog)
}

sig Boolean, Integer, Real, Character, Stringz extends Type{}


// Standalone signatures for base entities
sig Definition_Condition{
--  assume:     one Proposition,
--  guarantee:      one Proposition,
--  property:       one ((assume -> guarantee) -> Proposition)
}

sig Handling_Condition{
--  assume:     one Proposition,
--  guarantee:      one Proposition,
--  property:       one ((assume -> guarantee) -> Proposition)
}

sig State{
--  input:  Port,                       -- Entry port consumption
--  output: Port                        -- Exit port production
}

sig Proposition{
--  precond:    ((Attribute -> Boundary) -> Boolean),
--  postcond:   ((Attribute -> Boundary) -> Boolean),
--  invariant:  ((Behaviour -> Boundary) -> Boolean)
}

sig Boundary{
--  valB:   one (Boolean -> State),
--  valI:   one (Integer -> State),
--  valR:   one (Real -> State),
--  valC:   one (Character -> State),
--  valS:   one (String -> State)
}


--__________ASSERTIONS: OPERATIONS SIMULATION_________

--__________addEntryExitTranAssn operation: TRANSFORM SIGN
assert addEntryExitTranAssn{
    all en, ex: Kind, t, t': Transform |
                some Kind and
                t'.entry = t.entry + en and
                t'.exit = t.exit + ex and
                t'.entry & t.exit = none and
                t.entry & t'.exit = none
}
check addEntryExitTranAssn for 6 but 2 Transform, 3 Kind, 1 Function expect 0


--__________addEntryExitFunAssn operation:  TRANSFORM SIGN
assert addEntryExitFunAssn{
    all en, ex: Kind, f, f': Function |
                some Kind and
                f'.entry = f.entry + en and
                f'.exit = f.exit + ex and
                f'.entry & f.exit = none and
                f.entry & f'.exit = none
}
check addEntryExitFunAssn for 6 but 2 Function, 3 Kind expect 0

--__________FACTS: STATES & OPERATIONS SIMULATION_______

--__________NoLoopedSig fact:   KIND, ROLE SIGN
fact NoLoopedSig {
    some Behaviour      and
    no iden & operation and  -- No behaviour loops back recursively
    no iden & feature            -- No Attribute loops back recursively
}

pred showP () {}
run showP for 5 expect 1

assert showA { no Definition_Condition }
check showA for 5 but 2 Transform, 2 Function expect 1
