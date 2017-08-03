module tests/test

open util/ordering[Time] as timeorder

sig PhoneNum{ }
sig emergencyNum extends PhoneNum{}

sig Time {}

abstract sig Event { pre,post: Time }

sig Device {
   connectedTo: Device->Time,
   num: PhoneNum
}

sig Connect extends Event {
   from, to: Device
} {
   // Precondition: different device
   from!=to
   // Precondition: "from" and "to" were both idle
   from.connectedTo.pre = none
   to.connectedTo.pre = none
   // "from" now talks to "to"; "to" now talks to "from"; everyone else stays the same
   from.connectedTo.post = to
   to.connectedTo.post = from
   // everyone else stays the same
   all d: Device-from-to | d.connectedTo.post = d.connectedTo.pre
}

sig Disconnect extends Event {
   from, to: Device
} {
   // Precondition: they were previously talking
   from.connectedTo.pre = to
   to.connectedTo.pre = from
   // afterwards, they're talking to no one
   from.connectedTo.post = none
   to.connectedTo.post = none
   // everyone else stays the same
   all d: Device-from-to | d.connectedTo.post = d.connectedTo.pre
}

sig Interrupt extends Event {
   from, to, other: Device
} {
   // Precondition: different device
   from!=to
   // Precondition: "from" was idle, but "to" was talking to "other"
   from.connectedTo.pre = none
   to.connectedTo.pre = other
   // "from" now talks to "to"; "to" now talks to "from"; "other" is disconnected
   from.connectedTo.post = to
   to.connectedTo.post = from
   other.connectedTo.post = none
   // everyone else stays the same
   all d: Device-from-to-other | d.connectedTo.post = d.connectedTo.pre
}

fact {
  // Initially, there are no connections
  let t=timeorder/first | no connectedTo.t
  // Between each time step, exactly one event occurs
  all t: Time-timeorder/last | let t'=t.next | some e:Event | (e.pre=t && e.post=t')
}

ShowInterestingOperation: run {
   some Connect
   some Disconnect
   some Interrupt
} for 3 but 4 Event, 5 Time expect 1

DoNotInterruptEmergency: check {
   no i:Interrupt | i.to.num in emergencyNum
} for 3 but 4 Event, 5 Time expect 1
