module tests/test

sig Sub { f: Int }
run { some Sub$ && some Sub$f  } expect 1
