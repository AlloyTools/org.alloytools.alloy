module tests/test55a[P]

sig Q extends P { nn: n } // Should NOT succeed when running from test55, and also should NOT succeed when running from test55a

run {} expect 1
