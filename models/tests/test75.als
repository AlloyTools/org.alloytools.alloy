sig Node { x: Node }
enum X { A, B, C }
enum Y { D, E, F }
run { A=first } expect 1
run { B=first } expect 0
run { C=first } expect 0
run { some n:Node | #n.x > 1 } expect 0
