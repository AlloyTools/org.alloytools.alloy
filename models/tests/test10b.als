module tests/test10b[p1,p2]

open tests/test10a[p2] as pm1p2

fun second [elem1:p1, elem2:p2] : p2 {
  pm1p2/identity [elem2]
}
