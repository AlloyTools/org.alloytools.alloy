module tests/test --- bug suggested by Marcelo Frias

sig A,B { }

fun clau[ R : (A + B) -> (A + B) ] : univ->univ { *R }

fun star[R : (A + B) -> (A + B) ] : univ->univ {
  let aa = A <: R :> A |
  let bb = B <: R :> B |
  let ab = A <: R :> B |
  let ba = B <: R :> A |
  (*aa . ab + iden). *(*bb .ba . *aa . ab ). *bb +
  (*bb . ba + iden). *(*aa .ab . *bb . ba ). *aa
}

pred test [R : (A + B) -> (A + B)] { clau[R] = star[R] }

assert noTest {all R : (A + B) -> (A + B) | test[R]}

check noTest for 2 expect 0
