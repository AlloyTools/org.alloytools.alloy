module tests/test

private open tests/test63a as x
sig n { }
run { some sa && some x/sa && some fa } expect 1
