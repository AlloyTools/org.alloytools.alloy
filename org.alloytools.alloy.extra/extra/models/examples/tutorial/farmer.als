module examples/tutorial/farmer

/*
 * The classic river crossing puzzle. A farmer is carrying a fox, a
 * chicken, and a sack of grain. He must cross a river using a boat
 * that can only hold the farmer and at most one other thing. If the
 * farmer leaves the fox alone with the chicken, the fox will eat the
 * chicken; and if he leaves the chicken alone with the grain, the
 * chicken will eat the grain. How can the farmer bring everything
 * to the far side of the river intact?
 *
 * authors: Greg Dennis, Rob Seater
 *
 * Acknowledgements to Derek Rayside and his students for finding and
 * fixing a bug in the "crossRiver" predicate.
 */

open util/ordering[State] as ord

/**
 * The farmer and all his possessions will be represented as Objects.
 * Some objects eat other objects when the Farmer's not around.
 */
abstract sig Object { eats: set Object }
one sig Farmer, Fox, Chicken, Grain extends Object {}

/**
 * Define what eats what when the Farmer' not around.
 * Fox eats the chicken and the chicken eats the grain.
 */
fact eating { eats = Fox->Chicken + Chicken->Grain }

/**
 * The near and far relations contain the objects held on each
 * side of the river in a given state, respectively.
 */
sig State {
   near: set Object,
   far: set Object
}

/**
 * In the initial state, all objects are on the near side.
 */
fact initialState {
   let s0 = ord/first |
     s0.near = Object && no s0.far
}

/**
 * Constrains at most one item to move from 'from' to 'to'.
 * Also constrains which objects get eaten.
 */
pred crossRiver [from, from', to, to': set Object] {
   // either the Farmer takes no items
   (from' = from - Farmer - from'.eats and
    to' = to + Farmer) or
    // or the Farmer takes one item
    (one x : from - Farmer | {
       from' = from - Farmer - x - from'.eats
       to' = to + Farmer + x })
}

/**
 * crossRiver transitions between states
 */
fact stateTransition {
  all s: State, s': ord/next[s] {
    Farmer in s.near =>
      crossRiver[s.near, s'.near, s.far, s'.far] else
      crossRiver[s.far, s'.far, s.near, s'.near]
  }
}

/**
 * the farmer moves everything to the far side of the river.
 */
pred solvePuzzle {
     ord/last.far = Object
}

run solvePuzzle for 8 State expect 1

/**
 * no Object can be in two places at once
 * this is implied by both definitions of crossRiver 
 */
assert NoQuantumObjects {
   no s : State | some x : Object | x in s.near and x in s.far
}

check NoQuantumObjects for 8 State expect 0