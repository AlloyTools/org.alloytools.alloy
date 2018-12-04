module models/examples/toys/CeilingsAndFloors


sig Platform {}
sig Man {ceiling, floor: Platform}

fact PaulSimon {all m: Man | some n: Man | n.Above[m]}

pred Above[m, n: Man] {m.floor = n.ceiling}

pred Geometry {no m: Man | m.floor = m.ceiling}

assert BelowToo' { Geometry => (all m: Man | some n: Man | m.Above[n]) }

assert BelowToo { all m: Man | some n: Man | m.Above[n] }

check BelowToo for 2 expect 1
check BelowToo' for 3 expect 1