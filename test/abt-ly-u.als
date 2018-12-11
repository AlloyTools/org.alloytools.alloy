//---------------------------------------------------------------------------------------


// Orignal declaration of the orded signature
/* 
sig Book {
   // For the finite case use lone instead of one
   nextS: one Book
} 
*/

one sig firstS in Book {}
one sig lastS in Book {}

fact {
 all s: Book | s !in s.^nextS
 //all s: Book | s = firstS or s in firstS.^nextS
 // Only for the finite case
 no lastS.nextS
}

/** first */
fun first: one Book { firstS }

/** last */
fun last: one Book { lastS }

/** return a mapping from each element to its predecessor */
fun prev : Book->Book { ~(nextS) }

/** return a mapping from each element to its successor */
fun next : Book ->Book { nextS }

/** return elements prior to e in the ordering */
fun prevs [s: Book]: set Book { s.^(~(nextS)) }

/** return elements following e in the ordering */
fun nexts [s: Book]: set Book { s.^(nextS) }


//---------------------------------------------------------------------------------------



abstract sig Target { }
sig Addr extends Target { }
abstract sig Name extends Target { }

sig Alias, Group extends Name { }

// new declaration of the orderd signature
sig Book {
	names: set Name,
	addr: names->some Target,
     // For the finite case use lone instead of one
     nextS: lone Book
} {
	no n: Name | n in n.^addr
	all a: Alias | lone a.addr
}

pred add [b, b': Book, n: Name, t: Target] {
	//t in Addr or some lookup [b, Name&t]
    t in Addr or some lookup [b, t]
	b'.addr = b.addr + n->t
}

pred del [b, b': Book, n: Name, t: Target] {
	no b.addr.n or some n.(b.addr) - t
	b'.addr = b.addr - n->t
}

fun lookup [b: Book, n: Name] : set Addr { 
  n.^(b.addr) & Addr 
}

pred init [b: Book]  { 
 no b.addr 
}

// Original trace spesification
/*
fact traces {
	init [first]
	all b: Book-last |
	//all b: Book |
	  let b' = b.nextS |
	    some n: Name, t: Target |
	      add [b, b', n, t] or del [b, b', n, t]
}
*/
// New trace spesification
fact traces1 {
	init [firstS]
}
fact traces2 {
	all b, b': Book |
        b' in b.nextS =>
	    (some n: Name, t: Target | add [b, b', n, t] or
                                                 del [b, b', n, t])
}

------------------------------------------------------
// Trace-Invariant added as fact.
// Proof of the trace-invariant have to be done in a previous step.
fact traceInv {
 all b: Book, t1, t2: Target |
     b in firstS.*nextS =>{
       t2 in t1.(b.addr) =>{
         t2 in Addr or (some t3: Target | t3 in Addr and t3 in t2.^(b.addr))
       }
     }
}
------------------------------------------------------

assert lookupYields {
	//all b: Book, n: b.names | some lookup [b,n]
    all b: Book, n: b.names | b in first.*nextS => some lookup [b,n]
}
// This should not find any counterexample.
check lookupYields for 4




