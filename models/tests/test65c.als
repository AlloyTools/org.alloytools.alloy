module tests/test

open util/ordering[Time] as tord

open util/ordering[unrolls] as uord

sig Time { }

let dynamic[x] = x one-> Time

let dynamicSet[x] = x -> Time

let then [a, b, t, t'] {
    some x:Time | a[t,x] && b[x,t']
}

sig unrolls {}

let while [cond, body, t, t'] {
   some time: unrolls ->one Time
   {
     first.time = t
     last.time = t'
     !cond[t']
     all u: unrolls - last | let t1 = u.time, t2 = (u.next).time | (cond[t1] => body[t1,t2] else t1 =t2)
  }
}

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
   some t:Time | Object.location.first=Near && while[notdone, crossRiver, tord/first, t]
} for 8 unrolls, 8 Time expect 1
