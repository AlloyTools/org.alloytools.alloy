module examples/case_studies/com

/*
 * Model of Microsoft Component Object Model (COM) query
 * interface and aggregation mechanism.
 *
 * For a detailed description, see:
 *   http://sdg.lcs.mit.edu/~dnj/publications/com-fse00.pdf
 *
 * author: Daniel Jackson
 */

open util/relation as rel

sig IID {}

sig Interface {
  qi : IID -> lone Interface,
  iids : set IID,
  // next two lines should use domain() or range() functions
  iidsKnown : IID,
  reaches : Interface
}{
  iidsKnown = dom[qi]
  reaches = ran[qi]
}

sig Component {
  interfaces : set Interface,
  iids : set IID,   // can't do iids = interfaces.Interface$iids
  first, identity : interfaces,
  eqs: set Component,
  aggregates : set Component
}

fact defineEqs {
  all c1, c2: Component |
    c1->c2 in eqs <=> c1.identity = c2.identity
}

fact IdentityAxiom {
  some unknown : IID | all c : Component |
    all i : c.interfaces | unknown.(i.qi) = c.identity
}

fact ComponentProps {
  all c : Component {
    c.iids = c.interfaces.iids
    all i : c.interfaces | all x : IID | x.(i.qi) in c.interfaces
  }
}

sig LegalInterface extends Interface { }
fact { all i : LegalInterface | all x : i.iidsKnown | x in x.(i.qi).iids}

sig LegalComponent extends Component { }
fact { LegalComponent.interfaces in LegalInterface }

fact Reflexivity { all i : LegalInterface | i.iids in i.iidsKnown }
fact Symmetry { all i, j : LegalInterface | j in i.reaches => i.iids in j.iidsKnown }
fact Transitivity { all i, j : LegalInterface | j in i.reaches => j.iidsKnown in i.iidsKnown }

fact Aggregation {
    no c : Component | c in c.^aggregates
    all outer : Component | all inner : outer.aggregates |
      (some inner.interfaces & outer.interfaces)
      && (some o: outer.interfaces | all i: inner.interfaces - inner.first | all x: Component  | (x.iids).(i.qi) = (x.iids).(o.qi))
    }

assert Theorem1 {
     all c: LegalComponent | all i: c.interfaces | i.iidsKnown = c.iids
     }

assert Theorem2 {
    all outer: Component | all inner : outer.aggregates |
        inner in LegalComponent => inner.iids in outer.iids
    }

assert Theorem3 {
    all outer: Component | all inner : outer.aggregates | inner in outer.eqs
    }

assert Theorem4a {
      all c1: Component, c2: LegalComponent |
         some (c1.interfaces & c2.interfaces) => c2.iids in c1.iids
    }

assert Theorem4b {
      all c1, c2: Component | some (c1.interfaces & c2.interfaces) => c1 in c2.eqs
      }

check Theorem1 for 3 expect 0
check Theorem2 for 3 expect 0
check Theorem3 for 3 expect 0
check Theorem4a for 3 expect 0
check Theorem4b for 3 expect 0
