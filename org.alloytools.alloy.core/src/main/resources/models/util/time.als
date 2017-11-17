open util/ordering[Time]

sig Time { }

let dynamic[x] = x one-> Time

let dynamicSet[x] = x -> Time

let then [a, b, t, t'] {
    some x:Time | a[t,x] && b[x,t']
}

let while = while3

let while9 [cond, body, t, t'] {
    some x:Time | (cond[t] => body[t,x] else t=x) && while8[cond,body,x,t']
}

let while8 [cond, body, t, t'] {
    some x:Time | (cond[t] => body[t,x] else t=x) && while7[cond,body,x,t']
}

let while7 [cond, body, t, t'] {
    some x:Time | (cond[t] => body[t,x] else t=x) && while6[cond,body,x,t']
}

let while6 [cond, body, t, t'] {
    some x:Time | (cond[t] => body[t,x] else t=x) && while5[cond,body,x,t']
}

let while5 [cond, body, t, t'] {
    some x:Time | (cond[t] => body[t,x] else t=x) && while4[cond,body,x,t']
}

let while4 [cond, body, t, t'] {
    some x:Time | (cond[t] => body[t,x] else t=x) && while3[cond,body,x,t']
}

let while3 [cond, body, t, t'] {
    some x:Time | (cond[t] => body[t,x] else t=x) && while2[cond,body,x,t']
}

let while2 [cond, body, t, t'] {
    some x:Time | (cond[t] => body[t,x] else t=x) && while1[cond,body,x,t']
}

let while1 [cond, body, t, t'] {
    some x:Time | (cond[t] => body[t,x] else t=x) && while0[cond,body,x,t']
}

let while0 [cond, body, t, t'] {
    !cond[t] && t=t'
}
