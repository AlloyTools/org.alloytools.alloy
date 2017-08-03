module util/boolean

/*
 * Creates a Bool type with two singleton subtypes: True
 * and False. Provides common boolean operations.
 *
 * author: Greg Dennis
 */

abstract sig Bool {}
one sig True, False extends Bool {}

pred isTrue[b: Bool] { b in True }

pred isFalse[b: Bool] { b in False }

fun Not[b: Bool] : Bool {
  Bool - b
}

fun And[b1, b2: Bool] : Bool {
  subset_[b1 + b2, True]
}

fun Or[b1, b2: Bool] : Bool {
  subset_[True, b1 + b2]
}

fun Xor[b1, b2: Bool] : Bool {
  subset_[Bool, b1 + b2]
}

fun Nand[b1, b2: Bool] : Bool {
  subset_[False, b1 + b2]
}

fun Nor[b1, b2: Bool] : Bool {
  subset_[b1 + b2, False]
}

fun subset_[s1, s2: set Bool] : Bool {
  (s1 in s2) => True else False
}
