

sig A {}
sig B extends A {}

--
-- A function defined to be total that is actually partial
--
fun foo[x:B] :  one A {none}

run { some x : B | no foo[x] } for 4 expect 1
