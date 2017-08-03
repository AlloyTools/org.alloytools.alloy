module tests/test

sig S {}

check { no S => no (iden-Int->Int) } for 3 S expect 0
