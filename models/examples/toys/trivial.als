//a trivial model whose command has no solution
module trivial

sig S {}

fact { 1=2 }

run {some S} expect 0
