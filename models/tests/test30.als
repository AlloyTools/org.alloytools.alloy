module tests/test // Example from Daniel Jackson's book

sig Name,Thing {}

sig Thing1 extends Thing {}
sig Thing2 extends Thing {}

sig Man in Thing {name:Name}
sig Island in Thing1 {name:Name}

// This should give an error, saying that 2 fields with the same name
// must not overlap in their first column.
