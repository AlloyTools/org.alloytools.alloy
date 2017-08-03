module tests/test

open util/time

one sig Light { brightness: dynamic[Int] }

let b = Light.brightness

pred incr [t, t': Time] {
    b.t' = b.t + 1
    t' = t.next
}

pred decr [t, t': Time] {
    b.t' = b.t - 1
    t' = t.next
}

pred incrThenReturnOld [out: Int, t,t': Time] {
    out = b.t
    b.t' = b.t + 1
    t' = t.next
}

let both = incr.then[decr]

let cond[t] = b.t > 0

run {
    some t:Time | some x:Int | { incrThenReturnOld[x].then[both].then[decr] [first, t] && b.t=x }
} for 7 Time expect 1

run {
    some t:Time | some x:Int | { incrThenReturnOld[x].then[decr].then[both].then[decr] [first, t] && b.t=x }
} for 7 Time expect 0

run {
    some t:Time | b.first=3 && while[cond, decr, first, t]
} for 7 Time expect 1

run {
    some t:Time | b.first=4 && while[cond, decr, first, t]
} for 7 Time expect 0
