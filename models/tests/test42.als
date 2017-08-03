module tests/test --- bug post submitted by Carlos Pacheco

sig Heap {
        roots : set Obj
}

sig Obj {
        linked : set Obj
}

fact {
        all h : Heap | univ.(^linked) in univ
}

pred show () {
        some h : Heap | ((some o : h.roots.^linked | o in o.^linked) and
(all o : h.roots.^linked | not o in o.linked ))
}

run show but 1 Heap
