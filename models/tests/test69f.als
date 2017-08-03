module tests/test

sig Sub { f: Int }
run { some Sub$ && some Sub$f  && some A$ } // expect "A$" not found
