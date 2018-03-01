module examples/algorithms/messaging

/*
 * Generic messaging among several nodes
 *
 * By default, messages can be lost (i.e. never become visible to the
 * recipient node) or may be arbitrarily delayed.  Also, by default
 * out-of-order delivery is allowed.
 */

open util/ordering[Tick] as ord
open util/relation as rel

sig Node {}

sig MsgState {
   // Node that sent the message
   from: Node,
   // Intended recipient(s) of a message; note that broadcasts are allowed
   to: set Node
}

sig Msg {
   state: MsgState,
   // Timestamp: the tick on which the message was sent
   sentOn: Tick,
   // tick at which node reads message, if read
   readOn: Node -> lone Tick
}{
  readOn.Tick in state.to
}

sig Tick {
   // The state of each node
   state: Node -> one NodeState,

   //
   // Definition of what each node does on this tick:
   //
   // Typically, a node would determine
   // the messages it sends and its next state, based on its current
   // state and the messages it reads.
   //

   // Messages that the node _can_ read in this tick, i.e. messages available
   // for reading at the beginning of this tick.  The messages that
   // the node actually reads are a subset of this set.  Determined by
   // constraints in this module.
   visible: Node -> Msg,

   // Messages that the node _actually reads_ in this tick.  Must be a subset
   // of visible.  Determined by constraints of the particular system
   // that uses this module.
   read: Node -> Msg,

   // Messages sent by the node in this tick.  They become visible to
   // (and can be read by) their recipients on the next tick.
   sent: Node -> Msg,

   // Messages available for sending at this tick.  A given message
   // atom is only used once, and then it gets removed from the available
   // set and cannot be used to represent messages sent on subsequent ticks.
   // Also, two different nodes cannot send the same message atom.
   // So, a message atom represents a particular single physical message
   // sent by a given node on a given tick.
   available: set Msg,

   // For each node, at each tick, the number of messages it _needs_ to send.
   // Used to rule out "proofs" of liveness violations that are caused
   // solely by not having enough messages available for sending.
   needsToSend: Node -> Msg
}

fun MsgsSentOnTick[t: Tick]: set Msg { t.sent[Node] }
fun MsgsVisibleOnTick[t: Tick]: set Msg { t.visible[Node] }
fun MsgsReadOnTick[t: Tick]: set Msg { t.read[Node] }

fact MsgMovementConstraints {
   // At the beginning, no messages have been sent yet
   no ord/first.visible[Node]

   // Messages sent on a given tick become visible to recipient(s)
   // on the subsequent tick.
   all pre: Tick - ord/last |
     let post = ord/next[pre] | {
        // messages sent on this tick are no longer available on subsequent tick
        post.available = pre.available - MsgsSentOnTick[pre]
     }

   all t: Tick | {
      // Messages sent on a tick are taken from the pool of available
      // (not-yet-sent) message atoms
      MsgsSentOnTick[t] in t.available

      // Timestamps are correct
      MsgsSentOnTick[t].sentOn in t
      MsgsReadOnTick[t].readOn[Node] in t

      // The only new message atoms are those sent by nodes
      MsgsSentOnTick[t] = t.sent[Node]

      all n: Node, m: Msg |
           m.readOn[n] = t => m in t.read[n]
      // Return addresses are correct
      all n: Node | t.sent[n].state.from in n

      // messages sent to a node on a tick become visible to that node on some subseqent tick,
      // and permanently stop being visible to that node on the tick after that node reads the message
      all n: Node, m: Msg | {
          // message starts being visible to node n no earlier than it is sent;
          // only messages sent to this node are visible to this node.
          (m in t.visible[n] => (n in m.state.to && m.sentOn in ord/prevs[t]))
          // message permanently stops being visible immediately after being read
          (m in t.read[n] => m !in ord/nexts[t].visible[n])
      }
   }
}

sig NodeState {
}

fun MsgsLiveOnTick[t: Tick]: set Msg {
  Msg - { future: Msg | future.sentOn in ord/nexts[t] }
           - { past: Msg | all n: past.state.to | past.readOn[n] in ord/prevs[t] }
}

pred TicksEquivalent[t1, t2: Tick] {
   t1.state = t2.state
   some r: (MsgsLiveOnTick[t1] - MsgsVisibleOnTick[t1]) one -> one (MsgsLiveOnTick[t2] - MsgsVisibleOnTick[t2])  |
       all m1: dom[r] | let m2 = m1.r | {
         m1.(Msg<:state) = m2.state
       }
   some r: MsgsVisibleOnTick[t1]  one -> one MsgsVisibleOnTick[t2]  |
       all m1: dom[r] | let m2 = m1.r | {
         m1.(Msg<:state) = m2.state
       }
}

pred Loop {
  some t: Tick - ord/last | TicksEquivalent[t, ord/last]
}

fact CleanupViz {
    // cleans up visualization without precluding any interesting traces

    // all messages must be sent
    Msg in Tick.sent[Node]
}

pred ReadInOrder  {
    //
    // This function ensures that messages are read in order.
    //

    // for all pairs of nodes
    all n1, n2: Node |
        // for all pairs of messages sent from n1 to n2
        all m1, m2: Msg |
            {
              m1.state.from = n1
              m2.state.from = n1
              m1.state.to = n2
              m2.state.to = n2
           } => {
            // if both m1 and m2 are read by n2, *and*
            // n2 reads m1 before m2, then m1 must have
            // been sent before m2
            (some m1.readOn[n2] && some m2.readOn[n2] &&
             m1.readOn[n2] in ord/prevs[m2.readOn[n2]]) =>
                ord/lte[m1.sentOn, m2.sentOn]
           }
}

fact ReadOnlyVisible { read in visible }

pred NoLostMessages {
  // this function ensures that messages will not
  // be lost, i.e. a message send to a node will
  // eventually be visible to that node
  all m: Msg |
    (m.sentOn != ord/last) => (all n: m.state.to |
      some t: ord/nexts[m.sentOn] |
        m in t.visible[n])
}

pred NoMessageShortage {
  // this function ensures that there will be
  // no shortage of messages in the available
  // message pool during the trace
  all t: Tick - ord/last |
    (sum n: Node | # t.needsToSend[n]) =< # t.available
}

pred SomeState  {
   # Node > 1
   //# Tick$read > 1
}

pred OutOfOrder  {
   ! ReadInOrder
   # Msg = 2
}

run SomeState for 2 expect 1
run OutOfOrder for 4 expect 1



// DEFINED VARIABLES
// Defined variables are uncalled, no-argument functions.
// They are helpful for getting good visualization.
fun FROM: Msg -> Node {{m: Msg, n: Node | n in m.state.from}}
fun TO: Msg -> Node {{m: Msg, n: Node | n in m.state.to}}
