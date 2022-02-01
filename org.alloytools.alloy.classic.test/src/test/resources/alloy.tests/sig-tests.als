sig B {}
sig A {
    fmand : B,
    fset : set B,
    flone : lone B,
    fsome : some B

}
sig E extends B {}
abstract sig F {}
sig G,H extends F {}


fmand_0:    run { some a : A | no a.fmand           } for 4 expect 0
fmand_1:    run { some a : A | # a.fmand = 1        } for 4 expect 1
fmand_2:    run { some a : A | # a.fmand > 1        } for 4 expect 0

fset_0:     run { some a : A | # a.fset =0          } for 4 expect 1
fset_1:     run { some a : A | # a.fset =4          } for 4 expect 1
fset_2:     run { some a : A | # a.fset =2          } for 4 expect 1
fset_3:     run { some a : A | # a.fset =2          } for 4 expect 1
fset_4:     run { some a : A | a.fset = B           } for 4 expect 1

flone_1:    run { some a : A | # a.flone = 1        } for 4 expect 1
flone_1:    run { some a : A | # a.flone > 1        } for 4 expect 0

fsome_0:    run { some a : A | # a.fsome = 0        } for 4 expect 0
flone_1:    run { some a : A | # a.fsome = 1        } for 4 expect 1
flone_2:    run { some a : A | # a.fsome > 1        } for 4 expect 1

fnoB:       run { some A and no B                   } for 4 expect 0

subset_1:   run { E in B                            } for 4 expect 1
subset_2:   run { some E implies some E & B         } for 4 expect 1


abstract_1: run { some F                            } for 4 expect 1
abstract_2: run { no G+H and some F                 } for 4 expect 0

abstract sig I {}
abstract_surprise: run { # I = 4                    } for 4 expect 1

sig C in Int {}
sig D in A {}

multipleinh_0:  run { some c : C | c = 1                } for 4 expect 1
multipleinh_1:  run { some d : D | d = 1                } for 4 expect 0
multipleinh_2:  run { some d : D | some d.fmand         } for 4 expect 1

