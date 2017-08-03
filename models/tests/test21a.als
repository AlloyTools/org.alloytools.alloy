module tests/test21a // Bugpost by nicolas.rouquette@jpl.nasa.gov

open util/relation as rel

abstract sig S1 {
    t : lone T1 + T2
}

sig T1 extends S1 {
    st : set T1 + T2
}{
    one t => t in st
}

abstract sig S2 extends S1 {
    ts : set T1 + T2
}

sig T2 extends S2 {
    sts : set T1 + T2
}{
    one t
    t in sts
}

run {} expect 1
