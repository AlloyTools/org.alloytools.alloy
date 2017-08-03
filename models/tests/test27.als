module tests/test[X]

fun add [a:Int, b:Int-a] : Int+X { int[a]+int[b] }

run add expect 1
