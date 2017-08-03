module tests/test

sig sa { fa: Int, private fb: Int }
private sig sb { ga: Int, private gb: Int }
run { some sa && some sb && some fa && some fb && some ga && some gb } expect 1
