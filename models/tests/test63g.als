module tests/test

private open tests/test63a as x
run { some x/sb } // should complain that the name cannot be found
