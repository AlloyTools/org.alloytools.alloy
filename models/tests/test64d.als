module tests/test

let a[x] = x+x
run { 4->4=a[4->4]   4=a[2] } expect 1

let apply2 [a,b] = a[b]
let inc [x] = x+1
run { some p:Int | p = apply2[inc,3] } expect 1

let apply3 [a,b,c] = a[b,c]
let add [x,y] = x+y
run { some p:Int | p = apply3[add,2,3] } expect 1
