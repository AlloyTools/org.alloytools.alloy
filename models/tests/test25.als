module tests/test // Bugpost by Sarfraz Khurshid

// The correct behavior
// is to generate an error message (saying recursion not supported).

sig S {}

pred p { p }

run p
