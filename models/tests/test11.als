module tests/test

fun add [a,b:Int] : Int { int[a]+int[b] }
fun union [a,b:univ] : univ { a+b }

fun test1:Int { 3.add[4] }
fun test2:univ { 3.union[4] }
fun test3:Int { 3+4 }

check { #test1=1 && #test2=2 && #test3=1 } expect 0
