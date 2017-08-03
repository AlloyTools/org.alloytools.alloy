module tests/test

fun add [a:Int, b:Int-a] : Int { int[a]+int[b] }

run add expect 1
