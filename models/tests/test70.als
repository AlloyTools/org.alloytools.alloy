module tests/test
one sig A { disj x, y: Int, disj p, q: Int }
run { x=y } expect 0
run { p=q } expect 0
