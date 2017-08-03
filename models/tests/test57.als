module tests/test57[N]

open tests/test57[Int] as go // This line should give an error "circular dependency"

sig P {}

run {}
