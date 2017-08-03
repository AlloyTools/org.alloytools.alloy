
sig Root {
  elems: seq A
}

sig A {
  moreElems: seq B
}

sig B {}

fun flatten[root: Root]: A {
  root.elems[0]
}

run {
  one Root 
  some r: Root | some flatten[r] 

} for 4
