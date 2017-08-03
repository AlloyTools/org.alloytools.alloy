module tests/test28[elem]

one sig Ord { First: elem }
fun first: elem { Ord.First }

run first expect 1
