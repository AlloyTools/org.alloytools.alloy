--option                noOverflow=false
--option.noOvflw_*      noOverflow=true

sig NonInt {}

equal:             run { 1=1                      } expect 1
equal2:            run { all n : Int | n = n      } expect 1
equal3:            run { some n : Int | n = 1     } expect 1

unequal:           run { 1!=1                       } expect 0
plus:              run { 1.plus[1]=2                } for 4 int expect 1
xplus:             run { 1.plus[1]!=2               } for 4 int expect 0
minus:             run { 1.minus[1]=0               } for 4 int expect 1
xminus:            run { 1.minus[1]!=0              } for 4 int expect 0
div:               run { 4.div[2]=2                 } for 4 int expect 1
xdiv:              run { 4.div[2]!=2                } for 4 int expect 0
div_min:           run { 4.div[-2]=-2               } for 4 int expect 1
xdiv_min:          run { 4.div[-2]!=-2              } for 4 int expect 0
mul:               run { 4.mul[2]=8                 } for 5 int expect 1
xmul:              run { 4.mul[2]!=8                } for 5 int expect 0
mul_min:           run { 4.mul[-2]=-8               } for 5 int expect 1
xmul_min:          run { 4.mul[-2]!=-8              } for 5 int expect 0

max_4:             run { 7 in Int and -8 in Int     } for 4 int expect 1

// TODO this fails but I think it should fail to compile
// noOvflw_max_4_9:  run { 9 in Int                 } for 4 int expect 0
// xmax_4:         run { 9 not in Int               } for 4 int expect 1

max_5:             run { 15 in Int and -16 in Int   } for 5 int expect 1
max_6:             run { 31 in Int and -32 in Int   } for 6 int expect 1
max_7:             run { 63 in Int and -64 in Int   } for 7 int expect 1
max_8:             run { 127 in Int and -128 in Int } for 8 int expect 1
max_9:             run { 255 in Int and -256 in Int } for 9 int expect 1

intinuniv:         run { all n : Int | n in univ    } for 4 int expect 1
intinident:        run { all n : Int | n->n in iden } for 4 int expect 1
inset:             run { 1 in  { n : Int | n = n }  } for 4 int expect 1
inset2:            run { 1 in  (-1+0+1+2)           } for 4 int expect 1
noother:           run { no n : Int | n in NonInt   } for 4 int expect 1

noOvflw_plus:      run { 6.plus[6]=-4               } for 4 int expect 0
okOverflow:        run { 6.plus[6]=-4               } for 4 int expect 1

pred solvesum[x,y,z : Int ] {
    x.plus[y] = z
}
solvesum_0:          run { some x,y,z : Int | solvesum[x,y,z]     } for 4 int expect 1
solvesum_1:          run { some x,y,z : Int | solvesum[x,y,z] and x > y and y > z    } for 4 int expect 1
