module tests/test

/*
 * The classic river crossing puzzle. A farmer is carrying a fox, a
 * chicken, and a sack of grain. He must cross a river using a boat
 * that can only hold the farmer and at most one other thing. If the
 * farmer leaves the fox alone with the chicken, the fox will eat the
 * chicken; and if he leaves the chicken alone with the grain, the
 * chicken will eat the grain. How can the farmer bring everything
 * to the far side of the river intact?
 *
 * authors: Felix Chang
 */

open util/time

/*
 * Defines 2 locations that Farmer, Fox, Chicken, and Grain can be at: Near or Far
 */
abstract sig Place { }
one sig Near, Far extends Place { }

/*
 * The farmer and all his possessions will be represented as Objects.
 */
abstract sig Object { location: dynamic[Place] }
one sig Farmer, Fox, Chicken, Grain extends Object {}

/*
 * Define what eats what when the Farmer' not around.
 * Fox eats the chicken and the chicken eats the grain.
 */
pred eats [a, b: Object] { a->b in Fox->Chicken + Chicken->Grain }

/*
 * This represents one move by the farmer; the farmer may bring at most one other object.
 * Also constrains that the move is only legal if nothing would get eaten as a result.
 */
pred crossRiver [t, t': Time] {
   t' = t.next
   some x:Object | {
      x.location.t != x.location.t'
      x!=Farmer => (x.location.t=Farmer.location.t && x.location.t'=Farmer.location.t')
      all y:Object-Farmer-x | y.location.t = y.location.t'
   }
   no p, q: Object | p.eats[q] && p.location.t'=q.location.t' && p.location.t'!=Farmer.location.t'
}

/*
 * The loop condition
 */
let notdone[t] = (Object.location.t != Far)

/*
 * the farmer moves everything to the far side of the river.
 */
run {
   some t:Time | Object.location.first=Near && while7[notdone, crossRiver, first, t]
} for 8 Time expect 1
