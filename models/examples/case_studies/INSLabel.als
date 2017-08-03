module examples/case_studies/INSLabel

/*
 * Models an Intentional Naming System (INS), a scheme for
 * dynamic resource discovery in a dynamic environment.
 *
 * For a detailed description, see:
 *   http://sdg.lcs.mit.edu/pubs/2000/INS_ASE00.pdf
 *
 * author: Sarfraz Khurshid
 */

sig Record {}

sig Label {}

sig Node {
  label: Label
}

sig LabelTree {
  root: Node,
  nodes: set Node,
  children: nodes one -> (nodes - root)
}
{ // connected
  nodes = root.*children
  some root.children
}

pred Get[db: DB, r: Record, a:Advertisement] {
  root[a] = root[db]
  nodes[a] =
    nodes[db]  & r.~(db.recs).*(~(db.children))
  anodes[a] =
    anodes[db] & r.~(db.recs).*(~(db.children))
  vnodes[a] =
    vnodes[db] & r.~(db.recs).*(~(db.children))
  all n: a.nodes |
      n.~(a.children) = n.~(db.children)
}

sig Attribute extends Label {}

sig Value extends Label {}

one sig Wildcard, Null extends Value {}

sig AVTree extends LabelTree {
  vnodes, anodes: set nodes
}
{
  root in vnodes
  root.label = Null
  Null !in (vnodes - root).label + anodes.label
  anodes.label in Attribute
  vnodes.label in Value
  all n: nodes | all /* disj */ c,c': n.children |
    c.label != c'.label
  all a: anodes | a.children in vnodes && some a.children
  all v: vnodes | v.children in anodes
  no Wildcard.~label.children
}

one sig Query extends AVTree {}
{
  all a: anodes | one a.children
}

one sig Advertisement extends AVTree {}
{
  Wildcard !in vnodes.label
}

one sig DB extends AVTree {
  records: set Record,
  recs: (vnodes - root) some -> records
}
{
  Wildcard !in vnodes.label
  all a: anodes | no a.recs
  all v: vnodes {
    no v.children => some v.recs
    no v.recs & v.^(~children).recs }
  all a: anodes | all disj v,v': a.children |
    (no v.*children.recs & v'.*children.recs)
}

one sig State {
  conforms: Query -> Advertisement -> Node -> Node,
  lookup: DB -> Query -> Node -> Node -> Record
}

fact ConformsFixPoint {
  all q: Query | all a: Advertisement |
    all nq: Node | all na: Node |
      q.ConformsAux[a,nq,na] <=>
      {
       nq.label in Wildcard + na.label
       all nq': q.children[nq] | some na': a.children[na] |
         q.ConformsAux[a,nq',na']
      }
}

pred Query.ConformsAux[a: Advertisement, nq: Node, na: Node] {
  na in State.conforms[this][a][nq]
}

pred Conforms[q: Query, a:Advertisement] {
  q.ConformsAux[a, q.root, a.root]
}

fact LookupFixPoint {
  all db: DB, q: Query, T: Node, n: Node, r: Record |
    r in db.LookupAux[q,T,n] <=>                                  // record r is in the result if and only if
    {
     all na: n.(q.children) | all nv: na.(q.children) |            // for all child av-pairs (na,nv) of av-pair n in q
      some Ta: T.(db.children) {
         Ta.label = na.label                                       //  Ta is a child node with attribute na
         nv.label = Wildcard =>                                    //  wildcard matching
           r in Ta.^(db.children).(db.recs) else                     //   r is a record of any child of Ta
           (some Tv: Ta.(db.children) {                             //  normal matching
             Tv.label = nv.label                                   //   Tv is a child of Ta with value nv
             no nv.(q.children) =>                                 //   if Tv is a leaf-node
               r in Tv.*(db.children).(db.recs) else                   //        r is a record of Tv or of v
               r in db.LookupAux[q,Tv,nv] }) }                     //   else r is a record of the recursive call at Tv
    }
}

fun DB.LookupAux[q: Query, vd: Node, vq: Node]: set Record {      // helper function for Lookup
  State.lookup[this][q][vd][vq]
}

fun Lookup[db: DB, q: Query]: set Record {                             // models Lookup-Name algorithm invocation
  db.LookupAux[q, db.root, q.root]
}

assert LookupConforms2 { //soundness and completeness
  all q: Query | all db: DB | all r: Record | all a: Advertisement |
    Get[db,r,a] => // all n: a.nodes | n.~(db.children)
    {r in db.Lookup[q] <=> q.Conforms[a]}
}

// < 10 sec
check LookupConforms2 for 4 but 1 State, 3 LabelTree, 2 Record expect 0
// ~ 25 min
//check LookupConforms2 for 6 but 1 State, 3 LabelTree, 2 Record
//check LookupConforms2 for 6 but 1 State, 3 LabelTree, 3 Record
run Lookup for 3 expect 0
