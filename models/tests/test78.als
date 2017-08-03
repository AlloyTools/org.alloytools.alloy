module tests/test // Bug reported by Juan Pablo Galeotti <jgaleotti@dc.uba.ar>

sig A {}

one sig X,Y,Z,W extends A {}

one sig QF {
r1: A -> one A,
r2: A -> one A,
myVal: one A
}

run {
X.(QF.r1) =Y
 (QF.myVal).(QF.r1)=W
QF.r2 = QF.r1 ++ (QF.myVal->W)
} expect 1
