module bst

one sig BST {
  root: lone Node,
  size: lone Int
}

sig Node {
  key: lone Int,
  left, right: lone Node
}

pred Acyclic(t: BST) {
  all n: t.root.*(left + right) {
    n !in n.^(left + right)
    lone n.~(left + right)
    no n.left & n.right
  }
}

pred SizeOk(t: BST) {
  t.size = #t.root.*(left + right)
}

pred SearchOk(t: BST) {
  all n: t.root.*(left + right) {
    some n.key
    all m: n.left.*(left + right) | m.key.lt[n.key]
    all m: n.right.*(left + right) | m.key.gt[n.key]
  }
}

pred RepOk(t: BST) {
  Acyclic[t] 
  SizeOk[t] 
  SearchOk[t]
}

--pred NotRepOk(t: BST) {
  --!Acyclic[t] || !SizeOk[t] || !SearchOk[t]
--}

fact Reachability { BST.root.*(left + right) = Node }

fact NumKeysEqualsScopeForNode {
  all n: BST.root.*(left + right) | n.key.gt[-1] and n.key.lt[#Node]
}
--fact ConsecutiveKeysFrom0 {
--  0 in Node.key
--  all n: Node | n.key != 0 implies some m: Node | m.key = prev[n.key]
--}

count RepOk for exactly 8 Node, 5 int
--run NotRepOk for exactly 5 Node
