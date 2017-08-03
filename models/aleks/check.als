sig A { }
sig B { }
sig Relation1 { r : A -> B -> one (A+B) }
sig Relation2 { r : (A+B) one -> A -> B }
sig Relation3 { r : A -> (A+B) one -> B }

assert a1 {
    all r1: Relation1 | 
        all a: A |
            all b: B |
                one r1.r[a][b]
}

assert a2 {
    all r2: Relation2 | 
        all a: A |
            all b: B |
                one r2.r.b.a
}

assert a3 {
    all r3: Relation3 | 
        all a: A |
            all b: B |
                one r3.r.b[a]
}

check a1 for 3
check a2 for 3
check a3 for 3