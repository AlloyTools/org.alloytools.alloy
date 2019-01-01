sig A {}
run command {#A = 1 or #A = 2} for 10
assert proposition {some A or no A}
check proposition for 10

