module tests/test

open util/ternary as ut

sig A {x:A->A, y:A->A, z:A->A}

sig D {}

pred example {
  dom[x]!=mid[x]
  mid[x]!=ran[x]
  select12[x]!=select23[y]
  select12[x]!=select13[z]
  flip12[x]!=flip13[y]
  flip12[x]!=flip23[z]
}

run example for 3 but exactly 0 D
run example for 3 but exactly 5 D
run example for 3 but exactly 10 D
