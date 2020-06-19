module dllist

abstract sig Char {}
one sig a, b, c, d extends Char {}

one sig DLList {
  head: one Node,
  tail: one Node
}

sig Node {
  elem: lone Char,
  link: lone Node,
  previous: lone Node
}

pred RepOk(l: DLList) {
  no l.head.previous // head is first node
  no l.tail.link // tail is last node
  no l.head.elem // head is sentinel
  l.head.*link = l.tail.*previous // all nodes are reachable from head and tail
  all n: l.head.*link {
    n != l.head implies some n.elem // non-sentinel nodes have elements
    n !in n.^link // acyclic along link
    some n.link => n.link.previous = n // link and previous form 2-cycles
  }
}

fact Reachability { DLList.head.*link = Node }

count RepOk for exactly 7 Node, 5 int
