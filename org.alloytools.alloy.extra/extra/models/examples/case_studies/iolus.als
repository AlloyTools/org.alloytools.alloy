module examples/case_studies/iolus

/*
 * This is a model of Iolus, a scheme for secure multicasting.
 * In this scheme, nodes multicast messages to other nodes
 * within a group whose membership changes dynamically. The
 * group is partitioned into subgroups, arranged in a tree,
 * each with its own Key Distribution Server (KDS).
 *
 * For a detailed description, see:
 *   Mana Taghdiri, "Lightweight Modelling and Automatic Analysis
 *   of Multicast Key Management Schemes", Masters Thesis, Dept.
 *   of EECS, MIT, Dec. 2002.
 *   http://sdg.lcs.mit.edu/pubs/theses/taghdiri_masters.pdf
 *
 * author: Mana Taghdiri
 */

open util/ordering[Tick] as ord

sig Tick {}

/**
 * It can be abstract, since the fact below says Key=GroupKey
 */
abstract sig Key {}

/**
 * It can be abstract, since the fact below says Message=DataMessage
 */
abstract sig Message {
  sender : Member,
  sentTime : Tick,
  key : Key
}

/**
 * It can be abstract, since the fact below says KDS=GSA
 */
abstract sig KDS {
  keys : Tick -> Key,
  members : Tick -> Member
}{
  Monotonic[keys]
  all t : Tick | let t' = ord/prev[t] {
    all m : members[t]-members[t'] | Join[m, t, this]
    all m : members[t']-members[t] | Leave[m, t]
  }
}

/**
 * It can be abstract, since the fact below says "Member=Client"
 */
abstract sig Member {
  ownedKeys : Tick -> Key,
  receivedMessages : Tick -> Message
}{
  Monotonic[ownedKeys]
  Monotonic[receivedMessages]
}

fact MemberBehavior {
  Init[ord/first]
  all m : Member, t : Tick - ord/first |
    (some msg : Message |
      SendMessage[m, t, msg] || ReceiveMessage[m, t, msg]) ||
    (some kds : KDS | Join[m, t, kds]) ||
    Leave[m, t] || MemberInactive[m, t]
}

pred Monotonic[r : Tick -> univ] {
  all t : Tick | ord/prev[t].r in t.r
}

----------------------------------------------
sig GroupKey extends Key {
  generator : GSA,
  generatedTime : Tick
}{
  some c : Client |
   (Join[c, generatedTime, c.server] || Leave[c, generatedTime]) &&
   c.server = generator
}

sig DataMessage extends Message {
  gsaID : GSA,
  retransmitTime : Tick }
{ SendMessage[sender, sentTime, this] ||
  (some msg' : DataMessage |
     Remulticast[gsaID, msg', retransmitTime, this]) }

sig GSA extends KDS {
  parent : lone GSA }
{ keys[Tick].generator = this
  all t : Tick, k : keys[t] - keys[ord/prev[t]] |
    k.generatedTime = t }

sig Client extends Member {
  server : GSA }
{ all t : Tick, k : ownedKeys[t] - ownedKeys[ord/prev[t]] |
    k.generator = server && k.generatedTime = t }

fact IolusProperties {
  no k, k' : GroupKey | k!=k' && k.generator = k'.generator && k.generatedTime = k'.generatedTime
  all g : GSA, msg : DataMessage, t : Tick | RemulticastConditions[g, msg, t] =>
    (some msg': DataMessage | Remulticast[g, msg, t, msg'])
}

fact GSATree {
  let root = {g : GSA | no g.parent} {
    one root
    GSA in root.*~parent }}

fact {
  Member = Client
  KDS = GSA
  Message = DataMessage
  Key = GroupKey
  no m, m' : DataMessage {
    m!=m'
    m.sender = m'.sender
    m.sentTime = m'.sentTime
    m.key = m'.key
    m.gsaID = m'.gsaID
    m.retransmitTime = m'.retransmitTime }
}

----------------------------------------------
pred Init[t : Tick] {
  no Member.receivedMessages[t]
  no Member.ownedKeys[t]
  no KDS.keys[t]
  no KDS.members[t] }

pred Join[m : Member, t : Tick, kds : KDS] {
  kds = m.server
  JoinRequest[m, kds, t]
  NoChange[m.receivedMessages, t]
}
pred JoinRequest[c : Client, gsa : GSA, t : Tick] {
  c !in gsa.members[ord/prev[t]]
  KeyUpdate[gsa, t]
  c in gsa.members[t] }

pred Leave[m : Member, t : Tick] {
  LeaveRequest[m, m.server, t]
  NoChange[m.receivedMessages, t] }

pred LeaveRequest[c : Client, gsa : GSA, t : Tick] {
    c in gsa.members[ord/prev[t]]
    KeyUpdate[gsa, t]
    c !in gsa.members[t] }

pred SendMessage[m : Member, t : Tick, msg : Message] {
  SendRequest[m, m.server, t, msg]
  m.receivedMessages[t] = m.receivedMessages[ord/prev[t]] + msg
  ConstantMembership[m, t] }

pred SendRequest[c : Client, gsa : GSA, t : Tick, msg : DataMessage] {
  c in gsa.members[t]
  msg.sender = c
  msg.sentTime = t
  NewestKey[gsa.keys[t], msg.key]
  msg.gsaID = gsa
  msg.retransmitTime = t
  (some gsa.parent.members[t]) =>
    (some msg' : DataMessage | Remulticast[gsa, msg, t, msg']) }

pred ReceiveMessage[m : Member, t : Tick, msg : Message] {
  ReceiveConditions[m, t, msg]
  m.receivedMessages[t] = m.receivedMessages[ord/prev[t]] + msg }

pred MemberInactive[m : Member, t : Tick] {
  NoChange[m.receivedMessages, t] --does not constrain owned keys
  ConstantMembership[m, t] }

pred ReceiveConditions[m : Member, t : Tick, msg : Message] {
  ConstantMembership[m, t]
  msg !in m.receivedMessages[ord/prev[t]]
  msg.retransmitTime in ord/prevs[t]
  msg.key in m.ownedKeys[t] }

pred CanReceive[m : Member, t : Tick, msg : Message] {
  some msg' : DataMessage {
    msg'.sentTime = msg.sentTime
    msg'.sender = msg.sender
    msg' in m.receivedMessages[ord/prev[t]] || ReceiveConditions[m, t, msg'] }}

pred IsMember[m : Member, t : Tick] {
  some kds : KDS | m in kds.members[t]
}

-------------------------------------------
pred RemulticastConditions[g : GSA, msg : DataMessage, t : Tick] {
  msg.retransmitTime in ord/prevs[t]
  msg.key in g.keys[t] + g.parent.keys[t]
  some g.parent + g - msg.gsaID }

pred Remulticast[g : GSA, msg : DataMessage, t : Tick, msg': lone DataMessage] {
  RemulticastConditions[g, msg, t]
  let g' = g.parent + g - msg.gsaID | NewestKey[g'.keys[msg.sentTime], msg'.key]
  msg'.sender = msg.sender
  msg'.sentTime = msg.sentTime
  msg'.retransmitTime = t
  msg'.gsaID = g
}

pred KeyUpdate[g : GSA, t : Tick] {
  some k : Key {
    GeneratedKey[g, t, k]
    all c : Client | c in g.members[t] <=> k in c.ownedKeys[t]
    k in g.keys[t] }}

pred NewestKey[keys : set GroupKey, newest: lone GroupKey] {
  some keys <=> some newest
  newest in keys
  no ord/nexts[newest.generatedTime] & keys.generatedTime }

pred GeneratedKey[g : GSA, t : Tick, key : GroupKey] {
  key.generator = g
  key.generatedTime = t
}

pred ConstantMembership[c : Client, t : Tick] {
  IsMember[c, t] <=> IsMember[c, ord/prev[t]] }


pred NoChange[r : Tick -> univ, t : Tick] {
  r[ord/prev[t]] = r[t]
}

--------------------------------------------
assert Acyclic {
  all g : GSA | g !in g.^parent }

//check Acyclic for 6 -- one min

assert Connected {
  all g, g' : GSA | g in g'.*(parent + ~parent) }

//check Connected for 6

assert TimeProceeds {
  no msg : DataMessage | msg.retransmitTime in ord/prevs[msg.sentTime] }

//check TimeProceeds for 6

pred LoopFree {
  no t, t' : Tick {
    t!=t'
    all k : KDS | k.members[t] = k.members[t'] -- no constraint on keys
    all m : Member | m.receivedMessages[t] = m.receivedMessages[t']
    all m : DataMessage | m.retransmitTime = t =>
      (some m' : DataMessage {
        m'.retransmitTime = t'
        m.sender = m'.sender
        m.sentTime = m'.sentTime
        m.gsaID = m'.gsaID
        m.key = m'.key })
    }}

//fact NoLoop { LoopFree() } -- Property-specific diameter

------------------------------------------------
assert loop {
  !LoopFree }
//check loop for 13 but 2 Member, 1 KDS, 1 Message

assert NonLinearTopology {
  (no g : GSA | #g.~parent > 1) ||
  !(some m, m' : DataMessage | Remulticast[m.gsaID, m', m.retransmitTime, m]
    && !SendMessage[m.sender, m.sentTime, m]
    && (some c : Client | m in c.receivedMessages[ord/nexts[m.retransmitTime]]))}

//check NonLinearTopology for 5 but 3 KDS, 3 Member, 2 Message -- > good scenario

assert NotOutside {
  no msg : DataMessage | !IsMember[msg.sender, msg.sentTime] }

//check NotOutside for 5

assert Trivial {
  0 = 1 }

//check Trivial for 2 but 1 KDS

assert x {
  !(LoopFree && some DataMessage &&
     (some t : Tick | some m, m' : Member |
        m!=m' && IsMember[m, t] && IsMember[m', t] && t != ord/next[ord/first]))
}

//check x for 3 but 2 Member, 2 KDS, 2 Message
 -------------------------------------------
assert OutsiderCantRead {
  no msg : Message, m : Member, t : Tick {
    IsMember[msg.sender, msg.sentTime]
    !IsMember[m, msg.sentTime]
    CanReceive[m, t, msg]
  }
}
assert OutsiderCantSend {
  no msg : Message, m : Member, t : Tick {
    !IsMember[msg.sender, msg.sentTime]
    IsMember[m, t]
    msg !in m.receivedMessages[ord/prev[t]]
    CanReceive[m, t, msg]
  }
}
assert InsiderCanRead {
  all msg : Message, m : Member |
    some t : Tick - ord/last | all t' : ord/nexts[t] |
      (IsMember[msg.sender, msg.sentTime] &&
       IsMember[m, msg.sentTime]) => CanReceive[m, t', msg]
}

check OutsiderCantRead for 5 but 3 Member expect 0
//check OutsiderCantSend for 5 but 3 Member -- 5 min
//check InsiderCanRead for 9 but 2 Member, 1 KDS, 1 Message
//check InsiderCanRead for 10 but 2 Member, 2 KDS, 2 Message -- not able to check
