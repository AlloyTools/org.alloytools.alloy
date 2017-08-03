module examples/case_studies/chord

/*
 * Models the chord distributed hash table lookup protocol.
 *
 * For a detailed description, see:
 *   http://www.pdos.lcs.mit.edu/papers/chord:sigcomm01/
 */

sig Id {next: Id}
fact {all i: Id | Id in i.*next}

pred less_than [from, i,j: Id] {
   let next' = Id<:next - (Id->from) | j in i.^next'
}

pred less_than_eq [from, i,j: Id] {
   let next' = Id<:next - (Id->from) | j in i.*next'
}

sig Node {id: Id}
fact {all m,n: Node | m!=n => m.id != n.id}

sig NodeData {
   next: Node,
   finger: Id -> lone Node,
   closest_preceding_finger: Id -> one Node,
   find_successor: Id -> one Node
}

sig State {
   active: set Node,
   data: active -> one NodeData
}

fact {
   all s: State | all n: s.active |
      n.(s.data).next = n.(s.data).finger[n.id.next]
}

pred NextCorrect [s: State] {
   all n: s.active | let succ = n.(s.data).next {
      no n': s.active - n | less_than [n.id, n'.id, succ.id]
      succ != n || #s.active = 1
      succ in s.active
   }
}

pred FingersCorrect [s: State] {
   all nd: s.active.(s.data) | all start: (nd.finger).Node |
      nd.finger[start] in s.active &&
      (no n' : s.active | less_than [start, n'.id, nd.finger[start].id])
}

pred save_ClosestPrecedingFinger [s: State] {
   all n: s.active | let nd = n.(s.data) |
      all i: Id | let cpf = nd.closest_preceding_finger[i] {
   no n': (nd.finger[Id] + n) - cpf | less_than [cpf.id, n'.id, i]
   cpf in nd.finger[Id] + n
   cpf.id != i || # s.active = 1
      }
}

pred save_FindSuccessor[s: State] {
   all n: s.active | let nd = n.(s.data) | all i: Id {
      nd.find_successor[i] =
      (((less_than_eq [n.id, i, nd.next.id] && n.id != i) || # s.active = 1)
      => nd.next
      else
      (nd.closest_preceding_finger[i].(s.data).find_successor)[i])
   }
}

pred IrrelevantFact1   {
   all s : State {
      ClosestPrecedingFinger[s]
      FindSuccessor[s]
   }
}

pred ShowMe1Node  {
   #Node = 1
   all s : State | NextCorrect[s] && FingersCorrect[s]
   State.active = Node
}

run ShowMe1Node for 2 but 1 State, 1 Node expect 1

pred ShowMeGood  {
   #Id = 4
   all s : State | NextCorrect[s] && FingersCorrect[s]
   State.active = Node
}

run ShowMeGood for 4 but 1 State, 2 Node expect 1

pred FindSuccessorIsCorrect[s: State] {
   all i: Id | all n: s.active |
      let succ = (n.(s.data)).find_successor [i] {
         succ in s.active
         no n': s.active | less_than [i, n'.id, succ.id]
      }
}

pred ShowMeCorrectSuccessorEg {
   #Node = 3
   State.active = Node
   all s: State | FingersCorrect[s] && FindSuccessorIsCorrect[s]
}

run ShowMeCorrectSuccessorEg for 3 but 1 State expect 1

pred ShowMe3  {
   #Id = 5
   #Node = 3
   #State = 1
   all s : State | NextCorrect[s] && !FingersCorrect[s]
   State.active = Node
}

run ShowMe3 for 5 but 1 State expect 1

pred FindSuccessorWorks  {
   IrrelevantFact1
   ! (
      all s: State | FingersCorrect[s]
      => FindSuccessorIsCorrect[s]
   )
}

assert StrongerFindSuccessorWorks {
   all s: State | NextCorrect[s] => FindSuccessorIsCorrect[s]
}

run FindSuccessorWorks for 4 but 1 State expect 0
check StrongerFindSuccessorWorks for 4 but 1 State expect 1

/*
\section Variations

In the pseudocode presented in [\cite{chord1},
\cite{chord2}], there is some ambiguity as to what the
expression \tt<(n, n.successor]> means in boundary cases
where there is exactly one node and \tt<n.successor = n>.
The intention of the authors is that the set includes
\tt<n>. We consider variations of the alloy model with the
bug where the set \tt<(n, n]> does not include \tt<n>, and
observe how it affects the \tt<closest_preceding_finger> and
the \tt<find_sucessor> routines.

\subsection faulty \tt<closest_preceding_finger>

Suppose we change \tt<ClosestPrecedingFinger> as follows:

\code
*/

pred ClosestPrecedingFinger [s: State] {
   all n: s.active | let nd = n.(s.data) |
      all i: Id | let cpf = nd.closest_preceding_finger[i] {
   no n': (nd.finger[Id] + n) - cpf | less_than [cpf.id, n'.id, i]
   cpf in nd.finger[Id] + n
   cpf.id != i
      }
}

/*
The only change here is in the last line
\cite{cpf-variation}, where we removed the clause \tt< || #
s.active=1>. The assertion \tt<FindSuccessorWorks> will
still hold for scope up to 4, but \tt<ShowMe1Node> will fail
to generate an example! This is an example of a
over-constraint, where the inconsistency only shows up when
there is exactly one node. What happens here is that the
model requires that a closest preceding finger node has a
distinct identifier from the input identifier, but this
cannot happen if there is exactly one node and if the input
identifer equals that of the node.

\subsection faulty \tt<find_successor>

Consider the following pseudocode segment from [\cite{chord2}]:

n.find_successor(id)
  if (id in (n, n.successor])
    return n.successor;
  else
    n' = closest_preceding_finger(id);
    return n'.find_successor(id);

In the buggy scenario with a single node, the \tt<if> loop
always terminates at \cite{if-condition1}, leading to an
infinite loop.

Consider the corresponding change to \tt<FindSuccessor> as follows:

*/

pred FindSuccessor[s: State] {
   all n: s.active | let nd = n.(s.data) | all i: Id {
      nd.find_successor[i] =
      ((less_than_eq [n.id, i, nd.next.id] && n.id != i)
      => nd.next
      else
      (nd.closest_preceding_finger[i].(s.data).find_successor)[i])
   }
}

/*
The only change here is in the fourth line
\cite{sf-variation}, where we removed the clause \tt< || #
s.active = 1>. For the same reason, the \tt<if> loop
in this case always proceeds to the \tt<else> clause,
and since \tt<closest_preceding_finger> always returns
\tt<n> (the only node in the network), we end up
with a tautological statement:

\code
  nd.find_successor[i] = n.s.data.find_successor)[i]

This means that there is no additional constraint placed on
\tt<find_successor>, other than that its return type is
\tt<Node>. Now, if there is no distinction between active
and inactive nodes, that is, we have exactly one active node
in the network and no inactive ones, \tt<find_successor>
will return the right answer due to the type constraint,
therefore obscuring the bug. On the other hand, since we
have introduced inactive nodes, the assertion
\tt<FindSuccessorWorks> now fails with exactly one active
node and some inactive node(s), with \tt<find_successor>
returning an inactive node.
*/
