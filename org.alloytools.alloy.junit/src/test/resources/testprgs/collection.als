
open util/ordering[Trace] as trace

abstract sig boolean extends Object {}
one sig false, true extends boolean {}

sig null in Object {}
sig void in Object {}
sig Object {}
sig Element extends Object {}

enum Op { INIT, ADD,REMOVE,CLEAR}

sig Collection extends Object {
    elements : set Element,
    size     : Int,
    isEmpty  : boolean,
    contains : set Element
} {
    size = # elements
    isEmpty = (no elements => true else false)
    contains = elements
}



pred Collection.init {
    no this.elements
}

pred add[ c,c':Collection, result : boolean, a: Element ] {
    c'.elements = c.elements + a
    result = (a in c.elements => true else false)
}

pred remove[ c,c':Collection, result : boolean, a: Element ] {
    c'.elements = c.elements - a
    a in c.elements => result=true else result=false
}


pred clear[ c,c':Collection ] {
    no c'.elements
}

------------------------------------------------------------

pred syntax[t :Trace, o : Op] {
    t.op = o
    t.receiver in Collection
    no t.args
}
pred syntax[t :Trace, o : Op, domain0 : set univ] {
    t.op = o
    t.receiver in Collection
    t.args[0] in domain0
    # t.args = 1
}

pred syntax[t:Trace,o:Op,domain0,domain1 : set univ] {
    t.op = o
    t.receiver in Collection
    t.args[0] in domain0
    t.args[1] in domain1
    # t.args = 2
}

pred init[s:Trace] {
    s.op=INIT
    no s.result 
    no s.args
    one s.receiver
    s.receiver in Collection
    no s.receiver.elements
}


pred add[ s, s' : Trace ] {
    syntax[s', ADD, Element]
    add[ s.receiver, s'.receiver, s'.result, s'.args[0]]
}

pred remove[ s, s' : Trace ] {
    syntax[s', REMOVE, Element]
    remove[s.receiver, s'.receiver, s'.result, s'.args[0]]
}

pred clear[ s, s' : Trace ] {
    syntax[s', CLEAR]
    clear[s.receiver,s'.receiver]
    no s'.result
}

sig Trace {
    receiver: Object,
    op  : Op,
    args    : seq Object,
    result  : lone Object   
}

fact Trace {
    init[trace/first]

    all t' : Trace - trace/first, t : t'.prev {
        remove[t,t'] or add[t,t'] or clear[t,t']        
    }
}

run t1 { 
    some t : Trace | t.op = ADD and t.result=true and t.receiver.size=6

} for 15 but 5 int

