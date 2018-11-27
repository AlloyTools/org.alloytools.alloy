module models/examples/toys/CeilingsAndFloors


sig Platform {}
sig Man {ceiling, floor: Platform}

fact PaulSimon {all m: Man | some n: Man | n.Above[m]}

pred Above[m, n: Man] {m.floor = n.ceiling}

assert BelowToo { all m: Man | some n: Man | m.Above[n] }

check BelowToo for 2 expect 1
