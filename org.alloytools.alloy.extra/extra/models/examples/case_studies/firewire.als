module examples/case_studies/firewire

/*
 * A model of leader election in the Firewire protocol.
 *
 * Adapted from:
 *   [DG+01] M.C.A. Devillers, W.O.D. GriAEoen, J.M.T Romijn, and F.W. Vaandrager.
 *   Verification of a leader election protocol -- formal methods applied to IEEE
 *   1394. Technical Report CSI-R9728, Computing Science Institute, University of
 *   Nijmegen, December 1997. Also, Formal Methods in System Design, 2001.
 *
 * This model describes a leader election protocol used in Firewire, an IEEE
 * standard for connecting consumer electronic devices. The model is a
 * straightforward translation into Alloy of a model [DG+01] developed in Lynch's
 * IO Automata which has been analyzed using PVS, a theorem prover, but which, as
 * far as we know, has not been subjected to fully automatic analysis. We are able
 * to express the key correctness property -- that exactly one leader is elected
 * -- more directly, as a trace property rather than a refinement property, and
 * can check it without the need for the 15 invariants used in the more
 * traditional proof. And the analysis does not hardwire
 * a particular topology, so would be tricky to do with a standard model checker.
 *
 * The network is assumed to consist of a collection of nodes connected by
 * links. Each link between a pair of nodes is matched by a link in the other
 * direction. Viewing a link and its dual as a single, undirected edge, the
 * network as a whole is assumed to form a tree. The purpose of the algorithm is
 * to construct such a tree; in the model, this is achieved by labelling some
 * subset of the links as parent links (each pointing from a node to its parent),
 * and by marking a single node as the root.
 *
 * The algorithm, described in detail elsewhere [DG+01], works briefly as
 * follows. When a node detects that all of its incoming links (or all but one)
 * has been marked as a parent link, it sends a message on each outgoing link,
 * either an acknowledgment (indicating its willingness to act as parent), or a
 * request (indicating its desire to be a child), according to whether the dual of
 * the outgoing link has been marked or not. Leaf nodes (with only one incoming
 * link) may thus initiate the algorithm by sending requests to their adjacent
 * nodes. Performing this action changes a node's status from {\em waiting} to
 * {\em active}. A node that is still waiting, and which receives a message on a
 * link, may label that link a parent link. Once active, a node that receives an
 * acknowledgment on a link may also label the link, but if it receives a request,
 * instead changes its node status to {\em contending}. The resolving of
 * contentions is modelled simplistically by a single action that arbitrarily
 * labels one of the two links a pair of contending nodes. Finally, a node all of
 * whose incoming links are parent links designates itself a root.
 *
 * The specification is given below. Each signature introduces a basic type
 * and some relations whose first column has that type:
 *
 * \begin{itemize}
 *
 * \item {\em Msg} represents the type of messages. {\em Req} is the request
 * message and {\em Ack} is the acknowledgment message; these are actually
 * declared as singleton (keyword {\em static}) subsets of {\em Msg}, the set of
 * all messages, that form a partition (keyword {\em part}).
 *
 * \item {\em Node} represents the nodes of the network. The relations {\em to}
 * and {\em from} associate each node with a set of incoming and outgoing links
 * respectively.
 *
 * \item {\em Link} represents the links. The relations {\em target} and {\em
 * source} map a link to its end nodes; {\em reverse} maps a link to its dual. The
 * facts in the signatures {\em Node} and {\em Link} ensure that all these
 * relations are consistent with one another: that the incoming links of a node
 * are those whose target is that node, etc.
 *
 * \item {\em Op} introduces a set of names for the operations of the
 * protocol. This is merely for convenience; it allows us to ask for an execution
 * in which named operations occur, or example.
 *
 * \item {\em State} represents the global states. Each state has a partition of
 * the nodes into one of four statuses: {\em waiting} to participate, {\em active}
 * (having sent messages on outgoing links), {\em contending} (having sent a
 * request on a link and received a request on its dual), and {\em elected}
 * (having designated itself as a root). A set of links are labelled as parent
 * links. There is a message queue associated with each link. Finally, the state
 * is associated with the operation that produced it.
 *
 * \item {\em Queue} represents the message queues. Each queue has a slot that
 * optionally contains a message; the relation {\em slot} is a partial function
 * from queues to messages. In our first attempt at a model, we represented a
 * queue as a sequence (a partial function from a prefix of the integers to
 * messages), but having checked that no queue ever contained more than one
 * message, we simplified the model. The {\em overflow} field is included just in
 * case this was a mistake; a write to a queue that already contains a message
 * puts an arbitrary value there, which is easily detected.
 *
 * \end{itemize}
 *
 * The {\em facts} record the assumptions about the topology. The one named {\em
 * Topology} says that there is some partial function on nodes and some root such
 * that (1) every node is reachable from the root ({\tt *r} being the reflexive
 * transitive closure of the relation {\tt r}); (2) there are no cycles (expressed
 * by saying that the transitive closure has no intersection with the identity
 * relation on nodes); and (3) the relation obtained by following the {\em source}
 * relation backwards (from a node to the link for which it is a source), and then
 * the {\em target} relation forwards (from the link to its target) is this
 * relation, plus its transpose (so that each tree edge becomes two
 * links). Although the quantifier appears to be higher-order, it will be
 * skolemized away by the analyzer.
 *
 * The {\em functions} of the model are parameterized formulas. The function {\em
 * Trans} relates a pre-state {\tt s} to a post-state {\tt s'}. It has a case for
 * each operation. Look at the clause for the operation {\em WriteReqOrAck}, for
 * example. If this operation is deemed to have occurred, each of the constraints
 * in the curly braces must hold. The first says that the labelling of links as
 * parent links is unchanged. The second constraint (the quantified formula)
 * constrains with respect to the node at which the operation occurs. The
 * subformulas, from first to last, say that the node belongs to the waiting set
 * before and the active set afterwards; that there is at most one ({\em sole})
 * link that is incoming but not a parent link in the pre-state; that there are no
 * changes to node status except at this node; that a message is queued onto each
 * outgoing link; and that queues on all other links are unchanged.
 *
 * An 'invoked' function is simply short for the formula in its body with the
 * formal arguments replaced by the actual expressions. {\em WriteQueue}, for
 * example, says that if the queue's slot is not filled in the pre-state, then the
 * new queue in the post-state (given the local name {\tt q}) contains the message
 * {\tt m} in its slot, and has no message in its overflow. Otherwise, some
 * message is placed arbitrarily in the overflow, and the slot is
 * unconstrained. In {\em WriteReqOrAck}, the arguments {\tt s} and {\tt s'} are
 * bound to the {\tt s} and {\tt s'} of {\em Trans}; {\tt x} is bound to one of
 * the outgoing links from the set {\tt n.from}; and {\tt msg} is bound either to
 * the acknowledgment or request message.
 *
 * The function {\em Execution} constrains the set of states. It makes use of a
 * library module that defines a polymorphic ordering relation. The expression
 * {\tt Ord[State]} gives an ordering on all states. The two formulas of the
 * function say that {\tt Initialization} holds in the first state, and that any
 * pair of adjacent states is related by {\tt Trans}. The function {\em NoRepeats}
 * adds the constraints that there are no equivalent states in the trace, and that
 * no stuttering occurs.
 *
 * The three assertions are theorems for which the analyzer will search for
 * counterexamples. They assert respectively that: in every state of the trace,
 * there is at most one node that has been elected; that there is some state in
 * which a node has been elected; and that no queue overflows.
 *
 * The rest of the model is a collection of commands executed to find instances of
 * the functions or counterexamples to the theorems. We started by presenting a
 * variety of functions as a sanity check; here, only one is given, that asks for
 * an execution involving 2 nodes, 4 links, 4 queues and a trace of 6 states. The
 * standard semantics of these {\em scope} declarations in Alloy is that the
 * numbers represent an upper bound, so an instance may involve fewer than 4
 * queues, for example. The ordering module (not shown here), however, for
 * technical reasons, constrains the ordered set to match its scope, so a trace
 * with fewer than 6 states will not be acceptable.
 *
 * We then established some bounds on the diameter of the state machine for
 * various topology bounds. For 2 nodes and 2 links, for example, there are no
 * non-repeating traces of length 4; checking traces of length 3 is thus
 * sufficient in this case. The number of queues was limited to 5, to accommodate
 * the empty queue, a queue containing an {\tt Ack} or {\tt Req}, and each of
 * these with overflow. For 3 nodes and 6 links, a trace length of 8 suffices.
 *
 * We then checked that for these various topology bounds, the queues never
 * overflow. Finally, we checked the correctness properties, taken advantage of
 * the earlier results that justify the short traces and queues. We are thus able
 * to verify the properties for all topologies involving the given number of nodes
 * and links, without any assumptions about trace length, queue size or the
 * particular topological structure.
 *
 * author: Daniel Jackson
 * visualization: Robert Seater
 */

open util/ordering[State] as ord

abstract sig Msg {}
one sig Req, Ack extends Msg {}

sig Node {to, from: set Link} {
  to = {x: Link | x.target = this}
  from = {x: Link | x.source = this}
  }

sig Link {target, source: Node, reverse: Link} {
  reverse.@source = target
  reverse.@target = source
  }

/**
 * at most one link between a pair of nodes in a given direction
 */
fact {no x,y: Link | x!=y && x.source = y.source && x.target = y.target}

/**
 * topology is tree-like: acyclic when viewed as an undirected graph
 */
fact Topology {
some tree: Node lone -> Node, root: Node {
  Node in root.*tree
  no ^tree & iden & Node->Node
  tree + ~tree = ~source.target
  }
}

sig Op {}
one sig Init, AssignParent, ReadReqOrAck, Elect, WriteReqOrAck,
ResolveContention, Stutter extends Op {}

sig State {
  disj waiting, active, contending, elected: set Node,
  parentLinks: set Link,
  queue: Link -> one Queue,
  op: Op -- the operation that produced the state
  } {
  waiting + active + contending + elected = Node
}

pred SameState [s, s': State] {
  s.waiting = s'.waiting
  s.active = s'.active
  s.contending = s'.contending
  s.elected = s'.elected
  s.parentLinks = s'.parentLinks
  all x: Link | SameQueue [s.queue[x], s'.queue[x]]
  }

pred Trans [s, s': State] {
  s'.op != Init
  s'.op = Stutter => SameState [s, s']
  s'.op = AssignParent => {
    some x: Link {
      x.target in s.waiting & s'.waiting
      NoChangeExceptAt [s, s', x.target]
      ! IsEmptyQueue [s, x]
      s'.parentLinks = s.parentLinks + x
      ReadQueue [s, s', x]
      }}
  s'.op = ReadReqOrAck => {
    s'.parentLinks = s.parentLinks
    some x: Link {
      x.target in s.(active + contending) & (PeekQueue [s, x, Ack] => s'.contending else s'.active)
      NoChangeExceptAt [s, s', x.target]
      ! IsEmptyQueue [s, x]
      ReadQueue [s', s, x]
      }}
  s'.op = Elect => {
    s'.parentLinks = s.parentLinks
    some n: Node {
      n in s.active & s'.elected
      NoChangeExceptAt [s, s', n]
      n.to in s.parentLinks
      QueuesUnchanged [s, s', Link]
      }}
  s'.op = WriteReqOrAck => {
    -- note how this requires access to child ptr
    s'.parentLinks = s.parentLinks
    some n: Node {
      n in s.waiting & s'.active
      lone n.to - s.parentLinks
      NoChangeExceptAt [s, s', n]
      all x: n.from |
        let msg = (x.reverse in s.parentLinks => Ack else Req) |
          WriteQueue [s, s', x, msg]
      QueuesUnchanged [s, s', Link - n.from]
      }}
  s'.op = ResolveContention => {
    some x: Link {
      let contenders = x.(source + target) {
        contenders in s.contending & s'.active
        NoChangeExceptAt [s, s', contenders]
        }
      s'.parentLinks = s.parentLinks + x
      }
    QueuesUnchanged [s, s', Link]
    }
}

pred NoChangeExceptAt [s, s': State, nodes: set Node] {
  let ns = Node - nodes {
  ns & s.waiting = ns & s'.waiting
  ns & s.active = ns & s'.active
  ns & s.contending = ns & s'.contending
  ns & s.elected = ns & s'.elected
  }}

sig Queue {slot: lone Msg, overflow: lone Msg}

pred SameQueue [q, q': Queue] {
    q.slot = q'.slot && q.overflow = q'.overflow
  }

pred ReadQueue [s, s': State, x: Link] {
--  let q = s'.queue[x] | no q.(slot + overflow)
  no s'.queue[x].(slot + overflow)
  all x': Link - x | s'.queue[x'] = s.queue[x']
  }

pred PeekQueue [s: State, x: Link, m: Msg] {
  m = s.queue[x].slot
  }

pred WriteQueue [s, s': State, x: Link, m: Msg] {
        let q = s'.queue[x] |
  no s.queue[x].slot =>
    ( q.slot = m && no q.overflow) else
    some q.overflow
  }

pred QueuesUnchanged [s, s': State, xs: set Link] {
  all x: xs | s'.queue[x] = s.queue[x]
  }

pred IsEmptyQueue [s: State, x: Link] {
  no s.queue[x].(slot + overflow)
--  let q = s.queue[x] | no q.(slot + overflow)
  }

pred Initialization [s: State] {
  s.op = Init
  Node in s.waiting
  no s.parentLinks
  all x: Link | IsEmptyQueue [s, x]
  }

pred Execution  {
  Initialization [ord/first]
  all s: State - ord/last | let s' = ord/next[s] | Trans [s, s']
  }

pred ElectionHappens {
    Execution
        some s: State | some s.elected
    some s: State | no s.elected
}

pred NoRepeats {
  Execution
  no s, s': State | s!=s' && SameState [s, s']
  no s: State | s.op = Stutter
  }

pred NoShortCuts  {
  all s: State | -- remove this to speed up analysis - Ord[State].last - OrdPrev (Ord[State].last) |
    ! Trans [s, ord/next[ord/next[s]]]
  }

assert AtMostOneElected {
  Execution  => (all s: State | lone s.elected)
  }

assert OneEventuallyElected {
  Execution  => (some s: State | some s.elected)
  }

assert NoOverflow {
  Execution  => (all s: State, x: Link | no s.queue[x].overflow)
  }

run Execution for 7 Op, 2 Msg,
  2 Node, 4 Link, 4 Queue, 6 State expect 1

run ElectionHappens for 7 Op, 2 Msg,
  exactly 3 Node,  6 Link, 3 Queue, 7 State expect 1

-- solution for 3 State but not for 4 State
run NoRepeats for 7 Op, 2 Msg,
  2 Node, 2 Link, 2 Queue, 4 State expect 0

-- solution for 8 but not 9 State
run NoRepeats for 7 Op, 2 Msg,
    3 Node, 6 Link, 6 Queue, 8 State expect 0

-- only 5 queues needed: just count
-- no solution: establishes at most 3 queues needed
check NoOverflow for 7 Op, 2 Msg,
  3 Node, 6 Link, 5 Queue, 9 State expect 0

check AtMostOneElected for 7 Op, 2 Msg,
  3 Node, 6 Link, 3 Queue, 9 State expect 0

check OneEventuallyElected for 7 Op, 2 Msg,
  3 Node, 6 Link, 3 Queue, 9 State expect 1



// DEFINED VARIABLES
// Defined variables are uncalled, no-argument functions.
// They are helpful for getting good visualization.
fun queued: State -> Link -> Msg {
  {s: State, L: Link, m: Msg | m in L.(s.queue).slot}
}
