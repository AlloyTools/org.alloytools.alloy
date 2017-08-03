module tests/test

sig X { }

check { one sig$ && no field$ } expect 0  // since no user defined fields are defined
