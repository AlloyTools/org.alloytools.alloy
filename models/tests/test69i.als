module tests/test

sig X { y:Int }

check { one sig$ && one field$ } expect 0
