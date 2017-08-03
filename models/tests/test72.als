module tests/test

sig A { x, y, z: set Int }

run { (some p: field$ | some p.value) && (no x) && (no y) && (no z) } expect 0
run { (some p: field$ | some p.value) && (no x) && (some y) && (no z) } expect 1
run { (all p: field$ | some p.value) && (some x) && (no y) && (no z) } expect 0
run { (all p: field$ | some p.value) && (some x) && (some y) && (some z) } expect 1

run { (some p: A$x | some p.value) && (no x) && (some y) } expect 0
run { (some p: A$x | some p.value) && (some x) && (no y) } expect 1
run { (all p: A$x | some p.value) && (no x) && (some y) } expect 0
run { (all p: A$x | some p.value) && (some x) && (no y) } expect 1

check { A$x.value=x } for exactly 0 A expect 0
check { A$x.value=x } for exactly 1 A expect 0
check { A$x.value=x } for exactly 2 A expect 0
check { A$x.value=x } for exactly 3 A expect 0

run { (!lone A) && (some x) && (some y) } expect 1
