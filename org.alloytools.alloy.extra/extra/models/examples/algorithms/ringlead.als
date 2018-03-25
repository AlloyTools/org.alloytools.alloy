module examples/algorithms/ringlead

/*
 * Model of leader election on a ring
 *
 * Each process has a unique ID, IDs are ordered.
 * The algorithm elects the process with the highest
 * ID the leader, as follows.  First, each process
 * sends its own ID to its right neighbor.
 * Then, whenever a process receives an ID, if the
 * ID is greater than the process' own ID it forwards
 * the ID to its right neighbor, otherwise does nothing.
 * When a process receives its own ID that process
 * is the leader.
 */

open util/boolean as bool
open examples/algorithms/messaging as msg
open util/ordering[msg/Node] as nodeOrd
open util/ordering[msg/Tick] as tickOrd

sig RingLeadNode extends msg/Node {
   rightNeighbor: msg/Node
}

fact DefineRing {
  (one msg/Node || (no n: msg/Node | n = n.rightNeighbor))
  all n: msg/Node | msg/Node in n.^rightNeighbor
}

sig RingLeadMsgState extends msg/MsgState {
  id: msg/Node
}

sig MsgViz extends msg/Msg {
  vFrom: msg/Node,
  vTo: set msg/Node,
  vId: msg/Node
}

fact {
  MsgViz = msg/Msg
  vFrom = state.from
  vTo = state.to
  vId = state.id
}


sig RingLeadNodeState extends msg/NodeState {
  leader: Bool
}


pred RingLeadFirstTrans [self: msg/Node, pre, post: msg/NodeState,
                        sees, reads, sends, needsToSend: set msg/Msg] {
   one sends
   # needsToSend = 1
   sends.state.to = self.rightNeighbor
   sends.state.id = self
   post.leader = False
}

fact InitRingLeadState {
  all n: msg/Node |
    tickOrd/first.state[n].leader = False
}

pred RingLeadRestTrans [self: msg/Node, pre, post: msg/NodeState,
                       sees, reads, sends, needsToSend: set msg/Msg] {
   RingLeadTransHelper[self, sees, reads, sends, needsToSend]
   post.leader = True iff (pre.leader = True ||
                           self in reads.state.id)
}

pred RingLeadTransHelper[self: msg/Node, sees, reads, sends, needsToSend: set msg/Msg] {
   // we take any messages whose node ids are higher than ours,
   // and we forward them to the right neighbor.  we drop
   // all other messages.  if we get a message with our own
   // id, we're the leader.
   reads = sees

   all received: reads |
     (received.state.id in nodeOrd/nexts[self]) =>
       (one weSend: sends | (weSend.state.id = received.state.id && weSend.state.to = self.rightNeighbor))

   all weSend: sends | {
     let mID = weSend.state.id | {
       mID in nodeOrd/nexts[self]
       mID in reads.state.id
       weSend.state.to = self.rightNeighbor
     }
     //weSend.sentBecauseOf = { received : reads | received.id = weSend.id }
     //all otherWeSend: sends - weSend | otherWeSend.id != weSend.id
   }

   # needsToSend = # { m: reads | m.state.id in nodeOrd/nexts[self] }
}
fact RingLeadTransitions {
   all n: msg/Node {
      all t: msg/Tick - tickOrd/last | {
         t = tickOrd/first =>
           RingLeadFirstTrans[n, t.state[n], tickOrd/next[t].state[n], t.visible[n], t.read[n], t.sent[n], t.needsToSend[n]]
         else
           RingLeadRestTrans[n, t.state[n], tickOrd/next[t].state[n], t.visible[n], t.read[n], t.sent[n], t.needsToSend[n]]
      }
      // also constrain last tick
      RingLeadTransHelper[n, tickOrd/last.visible[n], tickOrd/last.read[n], tickOrd/last.sent[n], tickOrd/last.needsToSend[n]]
   }
}

assert OneLeader {
   all t: msg/Tick |
      lone n: msg/Node |
         t.state[n].leader = True
}

fact CleanupViz {
  RingLeadNode = msg/Node
  RingLeadMsgState = msg/MsgState
  RingLeadNodeState = msg/NodeState
}

pred SomeLeaderAtTick[t: msg/Tick] {
  some n: msg/Node | t.state[n].leader = True
}

pred NeverFindLeader {
  msg/Loop
  all t: msg/Tick | ! SomeLeaderAtTick[t]
}

assert Liveness {
  (msg/NoLostMessages && msg/NoMessageShortage) => ! NeverFindLeader
}

pred SomeLeader { some t: msg/Tick | SomeLeaderAtTick[t] }

assert LeaderHighest {
  all t: msg/Tick, n: msg/Node |
    t.state[n].leader = True => n = nodeOrd/last
}

run NeverFindLeader for 1 but 3 msg/Tick, 2 Bool, 2 msg/NodeState expect 1
check Liveness for 3 but 6 msg/Msg, 2 Bool, 2 msg/NodeState expect 0
check OneLeader for 5 but 2 Bool, 2 msg/NodeState expect 0
run SomeLeader for 2 but 3 msg/Node, 5 msg/Msg, 5 msg/Tick, 5 msg/MsgState expect 1
check LeaderHighest for 3 but 2 msg/NodeState, 5 msg/Msg, 5 msg/MsgState, 5 msg/Tick expect 0

