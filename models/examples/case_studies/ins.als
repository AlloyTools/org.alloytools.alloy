module examples/case_studies/ins

/*
 * Models an Intentional Naming System (INS), a scheme for
 * dynamic resource discovery in a dynamic environment.
 *
 * For a detailed description, see:
 *   http://sdg.lcs.mit.edu/pubs/2000/INS_ASE00.pdf
 *
 * author: Sarfraz Khurshid
 */

open util/relation as rel

sig Attribute {}
sig Value {}
sig Record {}

one sig Wildcard extends Value {}

sig AVTree {
  values: set Value,
  attributes: set Attribute,
  root: values - Wildcard,
  av: attributes one -> some (values - root),
  va: (values - Wildcard) one -> attributes
}{
  // values (and attributes) of tree are those reachable from root
  values = root.*(va.av)
}

sig Query extends AVTree {} {all a:attributes | one a.av}

sig DB extends AVTree {
  records : set Record,
  recs: (values - root) some -> records,
  lookup : Query -> (values -> records)
}{
  Wildcard !in values
}

fact AddInvariants {
  all db: DB {
    all v: db.values | no v.(db.recs) & v.^(~(db.av).~(db.va)).(db.recs)
    all a: db.attributes | all disj v1, v2: a.(db.av) |
      (some rr: *((db.va).(db.av)).(db.recs) | no v1.rr & v2.rr)
  }
}

pred Get [db: DB, r: Record, q: Query] {
  q.values = r.~(db.recs).*(~(db.av).~(db.va))
  q.attributes = q.values.~(db.av)
  q.root = db.root
  all a : attributes| a.~(q.va) = a.~(db.va)
  all v : values | v.~(q.av) = v.~(db.av)
}

pred Conforms [db: DB, q: Query, r: Record] {
  some p: Query {
    db.Get[r, p]
    q.va in p.va
    (q.av - Attribute -> Wildcard) in p.av
  }
}

pred indSubset[db : DB, q: Query, r: set Record, v: Value] {
  all a : v.(q.va) |
    (a.(q.av) in a.(db.av) => r in (a.(q.av)).(q.(db.lookup))) &&
    (a.(q.av) = Wildcard => r in a.(db.av).*((db.va).(db.av)).(db.recs))
}

pred Lookup[db: DB, q: Query, found: set Record] {
  all v: Value | not v.(q.va) in v.(db.va) => no v.(q.(db.lookup))
  all v: Value | all a : v.(q.va) |
    a.(q.av) != Wildcard && not a.(q.av) in a.(db.av) => no v.(q.(db.lookup))
  all v: Value - Wildcard |
    no v.(q.va) => v.(q.(db.lookup)) = v.*((db.va).(db.av)).(db.recs)
  all v: Value |
    some v.(q.va) => indSubset[db, q, v.(q.(db.lookup)), v] &&
    (no r: Record - v.(q.(db.lookup)) | indSubset[db, q, v.(q.(db.lookup)) + r, v])
  found = db.root.(q.(db.lookup))
}

assert CorrectLookup {
  all db: DB | all q : Query | all r : Record |
    Conforms [db,q,r] <=> db.Lookup[q, r]
}

pred Add [me: DB, adv: Query, r: Record, db: DB] {
  // restricted version - only advertisements with fresh attributes and values added
  no me.attributes & adv.attributes
  me.values & adv.values = me.root
  me.root = adv.root
  Wildcard !in adv.values
  r !in me.records
  db.values = me.values + adv.values
  db.attributes = me.attributes + adv.attributes
  db.root = me.root
  db.av = me.av + adv.av
  db.va = me.va + adv.va
  db.recs = me.recs + ((db.values - dom[db.va]) -> r)
}

pred RemoveWildCard[me: Query, q: Query] {
  q.values = me.values - Wildcard
  q.attributes = me.attributes - Wildcard.~(me.av)
  q.root = me.root
  q.av = me.av - Attribute -> Wildcard
  q.va = me.va - Value -> Wildcard.~(me.av)
}

assert MissingAttributeAsWildcard {
  all db : DB, q, q' : Query, found: set Record |
    db.Lookup[q, found] && q.RemoveWildCard[q'] => db.Lookup[q', found]
}
