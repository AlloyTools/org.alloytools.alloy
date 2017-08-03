module examples/case_studies/chord2

/*
 * Models the chord distributed hash table lookup protocol.
 *
 * For a detailed description, see:
 *   http://www.pdos.lcs.mit.edu/papers/chord:sigcomm01/
 */

open util/relation as rel

sig Id {next: Id}
fact {all i: Id | Id in i.*next}

/**
 * true iff i precedes j in the order starting at from
 */
pred less_than [from, i,j: Id] {
  let next' = Id<:next - (Id->from) | j in i.^next'  // if from=j, returns true if # nodes > 1
  }
pred less_than_eq [from, i,j: Id] {
  let next' = Id<:next - (Id->from) | j in i.*next'
  }

sig Node {id: Id}
fact {all m,n: Node | m!=n => m.id != n.id}

sig NodeData {
  prev, next: Node,
  finger: Id -> lone Node,
  closest_preceding_finger: Id -> one Node,
  find_predecessor: Id -> one Node,
  find_successor: Id -> one Node
  }

sig State {
  active: set Node,
  data: active -> one NodeData
  }

/**
 * node n's next node is defined to be the m where n's finger table maps the id
 * that follows n.id to m
 * next holds the first entry of the finger table
 */
fact {all s: State | all n: s.active | n.(s.data).next = n.(s.data).finger[n.id.next]}

pred NextCorrect [s: State] {
  all n: s.active {
    -- no intervening node (ie, close enough)
    no n': s.active - n | less_than [n.id, n'.id, n.(s.data).next.id]
    -- can reach all other active nodes (ie, far enough)
    -- need this because can't rule out case of next being node itself (because of 1-node ring)
    -- s.active in n.*(s.data.next)
    n.(s.data).next != n || #s.active = 1
    }
  }

/*
-- abortive attempt at simplifying next condition
fun NextCorrect" (s: State) {
  all n: s.active | let nx = s.data.next {
    s.active in n.*nx
    less_than (n.id, n.id, n.nx.id)
    }
  }
*/

pred NextCorrect' [s: State] {
-- next seems to be correct for 1,2,3 nodes
  all n: s.active | let nd = (s.data)[n] {
    let next' = Id<:next - (Id -> nd.next.id) {
      no n' : s.active { n'.id in n.id.^next' }
    }}
  }

assert Same1 {all s: State | NextCorrect[s] => NextCorrect'[s]}
//check Same1 for 3 but 1 State -- valid
assert Same2 {all s: State | s.active = Node => (NextCorrect'[s] => NextCorrect[s])}
//check Same2 for 3 but 1 State -- invalid if active condition removed

-- assert NextInFinger {all s: State | all n: s.active | some n.s.data.finger[n.id.next] }

/**
 * says that finger entry maps an id to a node so that there are no intervening nodes
 * between the id and the node
 */
pred FingersCorrect [s: State] {
  all nd: s.active.(s.data) | all start:nd.finger.univ |
    nd.finger[start] in s.active &&
    (no n' : s.active | less_than [start, n'.id, nd.finger[start].id])
  }

pred FingersCorrect' [s: State] {
  all n: s.active | let nd = (s.data)[n] | all start: Node.~(nd.finger) {
    nd.finger[start] in s.active &&
    (let next' = Id<:next - (nd.finger[start].id -> Id) {
      no n' : s.active - nd.finger[start] {
        n'.id in start.*next'
    }})}
  }

assert SameFC {all s: State | FingersCorrect [s] iff FingersCorrect'[s]}
//check SameFC for 3 but 1 State

pred ShowMeFC {
  all s : State | s.active = Node && FingersCorrect[s]
}

//run ShowMeFC for 2 but 1 State

/*
fun ClosestPrecedingFinger(s: State) {
  all n: s.active | let nd = n.s.data |
    all i: Id | let cpf = nd.closest_preceding_finger[i] {
      no n': nd.finger[Id] | less_than (cpf.id, n'.id, i)
      cpf in nd.finger[Id] + n
      less_than (n.id, cpf.id, i)
    }
  }
*/

pred ClosestPrecedingFinger_SAVE [s: State] {
  all n: s.active | let nd = n.(s.data) |
    all i: Id | let cpf = nd.closest_preceding_finger[i] {
      no n': (nd.finger[Id] + n) - cpf | less_than [cpf.id, n'.id, i]
      cpf in nd.finger[Id] + n
      cpf.id != i || # s.active = 1
      //less_than (n.id, cpf.id, i)
    }
  }

pred CPFBody [s: State, n: Node, nd: NodeData, i: Id, cpf: Node] {
  no n': (nd.finger[Id] + n) - cpf | less_than [cpf.id, n'.id, i]
  cpf in nd.finger[Id] + n
  cpf.id != i || # s.active = 1
  }
pred ClosestPrecedingFinger[s: State] {
  all n: s.active | let nd = n.(s.data) |
    all i: Id |
    some cpf: Node | CPFBody [s,n,nd,i,cpf] => CPFBody [s,n,nd,i,nd.closest_preceding_finger[i]]
  }

pred ClosestPrecedingFinger'[s: State] {
  all n: s.active | let nd = (s.data)[n] | all i: Id {
    let next' = Id<:next - (Id -> i) {
      nd.next.id in n.id.^next' =>
        // nd.closest_preceding_finger[i] = nd.next,
        (some n1: nd.finger[Id] {
          nd.closest_preceding_finger[i] = n1
          //n1 in nd.finger[Id]
          n1.id in n.id.^next'
          no n2: nd.finger[Id] | n2.id in n1.id.^next'
        }) else
      nd.closest_preceding_finger[i] = n
    }}
  }

assert SameCPF {all s: State | FingersCorrect[s] => (ClosestPrecedingFinger [s] iff ClosestPrecedingFinger' [s])}
assert SameCPF1 {all s: State | FingersCorrect[s] => (ClosestPrecedingFinger [s] => ClosestPrecedingFinger' [s])}
assert SameCPF2 {
  all s: State | ((s.active = Node && FingersCorrect[s] && ClosestPrecedingFinger' [s])
   => ClosestPrecedingFinger [s]) }
//check SameCPF for 3 but 1 State
//check SameCPF1 for 2 but 1 State
//check SameCPF2 for 3 but 1 State

pred ShowMeCPF  {
  all s : State | s.active = Node && FingersCorrect[s] &&
        // not ClosestPrecedingFinger(s) && ClosestPrecedingFinger'(s)
        ClosestPrecedingFinger[s]
  //all s : State | all nd : s.active.s.data | nd.finger[Id] = Node
  # Node = 2
  # State = 1
}

//run ShowMeCPF for 2 but 1 State

pred FindPredecessor[s: State] {
  all n: s.active | let nd = n.(s.data) | all i: Id {
    nd.find_predecessor[i] =
      ((less_than_eq [n.id, i, nd.next.id] && (n.id != i || # s.active = 1))
      => n
      else (nd.closest_preceding_finger[i].(s.data).find_predecessor)[i])
    }
  }
-- problem : could return node that's inactive ???

assert FPisActive {
  all s: State | FingersCorrect[s] && ClosestPrecedingFinger[s] && FindPredecessor[s]
  => (all n: s.active | all nd: n.(s.data) | nd.find_predecessor[Id] in s.active)
}

//check FPisActive for 3 but 1 State

pred FindPredecessor'[s: State] {
  all n: s.active | let nd = (s.data)[n] | all i: Id {
    let next' = Id<:next - (nd.next.id -> Id) {
      one s.active or i in n.id.^next' =>
      nd.find_predecessor[i] = n else
      nd.find_predecessor[i] =
      ((s.data)[nd.closest_preceding_finger[i]]).find_predecessor[i]
    }}
  }

assert SameFP {all s: State | FingersCorrect[s] && s.active = Node
  => (FindPredecessor [s] iff FindPredecessor' [s])}
assert SameFP1 {
  all s: State | FingersCorrect[s] && s.active = Node
    => (FindPredecessor [s] => FindPredecessor' [s])}
assert SameFP2 {
  all s: State | FingersCorrect[s] && s.active = Node
    => (FindPredecessor' [s] => FindPredecessor [s])}
//check SameFP for 3 but 1 State
//check SameFP1 for 3 but 1 State
//check SameFP2 for 3 but 1 State

pred FindSuccessor[s: State] {
  all n: s.active | let nd = (s.data)[n] | all i: Id {
    nd.find_successor[i] = ((s.data)[nd.find_predecessor[i]]).next
  }}

fact { all s : State {
    ClosestPrecedingFinger[s]
    FindPredecessor[s]
    FindSuccessor[s]
  }}

// should be able to //check that closest_p_f, etc returns
// only active nodes if FingersCorrect.

pred ShowMe1Node  {
  #Node = 1
  all s : State | NextCorrect[s]
  State.active = Node
}

//run ShowMe1Node for 2 but 1 State, 1 Node
-- does the expected correct thing for 1 node.

pred ShowMe1  {
  #Node = 2
  #State = 1
  all s : State | NextCorrect[s]
        State.active = Node
}

pred ShowMe2  {
  #Node = 3
  #State = 1
  all s : State | NextCorrect[s] && FingersCorrect[s]
        State.active = Node
  //all n: NodeData | one n.finger[Id]
}

assert OK1 {
  #Node = 3 &&
  #State = 1 &&
  (all s : State | NextCorrect[s] && FingersCorrect[s]) &&
  State.active = Node
}

assert FindSuccessorWorks {
  all s: State, i: Id |
    let nd = s.active.(s.data) |
    let succ = nd.find_successor [i] |
      FingersCorrect [s]
      => {
        no n': s.active | less_than [i, n'.id, succ.id]
        succ in s.active
        }
  }

check FindSuccessorWorks for 4 but 1 State, 3 Node, 3 NodeData expect 0
