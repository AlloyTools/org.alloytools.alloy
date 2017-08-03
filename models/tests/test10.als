module tests/test

open tests/test10b[A,B] as pm2AB

sig A {}

sig B {}

run { some A } expect 1

pred ex[disj a,b:Int] { a=b }

run ex expect 0

run identity expect 1
run pm2AB/pm1p2/identity expect 1
