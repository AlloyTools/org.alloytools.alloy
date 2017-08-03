module tests/test // Bugpost by C. M. Sperberg-McQueen <cmsmcq@acm.org>

abstract sig Component {}
abstract sig Step extends Component {}

sig Pipeline extends Component {}
sig Identity extends Step {}
sig XSLT extends Step {}
sig XInclude extends Step {}

run {some Pipeline} for 3 expect 1
run {some Pipeline} for 3 but 1 Pipeline expect 1
