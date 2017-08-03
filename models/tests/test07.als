module tests/test

run { some a:Int | a.int=3 } expect 1
run { some a:Int | int[a]=3 } expect 1
run { some a:Int | sum[a]=3 } expect 1
run { some a:Int | let b=int[a] | b.Int=a } expect 1
run { some a:Int | let b=int[a] | Int[b]=a } expect 1

sig X {}

check { #X=1 => (some a,b:X | disjoint[a,b]) } expect 1
check { #X=1 => (some a,b:X | b.(a.disj)) } expect 1

check { #X>1 => (some a,b:X | disj[a,b]) } expect 0
check { #X>1 => (some a,b:X | b.(a.disj)) } expect 0

check { #X=1 => (some a,b,c:X | disj[a,b,c]) } expect 1
check { #X=1 => (some a,b,c:X | c.(b.(a.disj))) } expect 1

check { #X=2 => (some a,b,c:X | disj[a,b,c]) } expect 1
check { #X=2 => (some a,b,c:X | c.(b.(a.disj))) } expect 1

check { #X>2 => (some a,b,c:X | disj[a,b,c]) } expect 0
check { #X>2 => (some a,b,c:X | c.(b.(a.disj))) } expect 0

check { some X => (some x:X | X+none =  X) } expect 0
check { some X => (some x:X | X+none != X) } expect 1
check {   no X => (some x:X | X+none =  X) } expect 1
check {   no X => (some x:X | X+none != X) } expect 1

check { some X => (all x:X | X+none =  X) } expect 0
check { some X => (all x:X | X+none != X) } expect 1
check {   no X => (all x:X | X+none =  X) } expect 0
check {   no X => (all x:X | X+none != X) } expect 0

