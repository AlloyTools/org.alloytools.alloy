module tests/test // Bugpost by Pierre Kelsen <pierre.kelsen@uni.lu>

sig A{}

fun empty(): set A { none }

run empty expect 1
