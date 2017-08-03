// SAT
// AA3:  8562 46965 21.000
// AA4: 13241 34497  1.665

// UNSAT
// AA3:  5669 28829 17.000
// AA4:  9848 25635  1.087

module tests/felix01/hashtable

// The system progresses over a number of time steps
open util/ordering[Time] as TO
sig Time {}

// Every key has a deterministic hash value
sig Key { hc: one Hashcode }
sig Value {}
one sig DefaultValue extends Value {}

// At any given time, every hashcode is associated with a sequence of buckets
sig Hashcode { buckets: (Int->Bucket) ->Time }

// Every bucket contains a Key and a Value.
sig Bucket { key:Key, value:Value }

fun read [k:Key, t:Time] : Value {
  let b = k.hc.buckets.t |
  (some i:indices[b] | get[b,i].key=k)
  =>
    {v:Value | (some i:indices[b] | get[b,i].key=k && get[b,i].value=v) }
  else
    DefaultValue
}

pred write [k:Key, v:Value, t,t':Time] {
  let oldlist = k.hc.buckets.t |
  let oldindex = { i:indices[oldlist] | get[oldlist,i].key=k } |
  some newbucket:Bucket | {
    newbucket.key=k
    newbucket.value=v
    buckets.t' = buckets.t ++ (k.hc)->oldlist.remove[oldindex].append[newbucket]
  }
}

pred init [t:Time] {
  no buckets.t
}

pred step [t,t':Time] {
  some k:Key, v:Value | write[k,v,t,t']
}

fact {
  init[TO/first]
  all t:Time-TO/last | let t'=t.next | step[t,t']
}

assert readwriteWorks {
  all k:Key, v:Value, t:Time-TO/last | let t'=t.next | write[k,v,t,t']=>read[k,t']=v
}

pred interesting {
  some k1,k2:Key |
  some v1,v2:Value-DefaultValue |
  let t0=TO/first |
  let t1=t0.next |
  let t2=t1.next |
  let t3=t2.next |
  k1!=k2 && v1!=v2 && k1.hc=k2.hc && write[k1,v1,t0,t1] && write[k1,v2,t1,t2] && write[k2,v2,t2,t3]
}

run interesting for 3 but 2 Hashcode, 4 Time, 3 int, 2 Key, 3 Value, 4 Bucket expect 1
check readwriteWorks for 3 but 2 Hashcode, 3 Time, 3 int, 2 Key, 3 Value, 4 Bucket expect 0

// METHODS on SEQUENCES

fun indices [x:Int->Bucket] : Int { x.Bucket }

fun get [x:Int->Bucket, i:Int] : Bucket { i.x }

fun remove [x:Int->Bucket, i:Int] : Int->Bucket {
  // Obviously this only works for lists that have 3 or fewer elements.
  i=Int[0] =>
    Int[0]->Int[1].x + Int[1]->Int[2].x
  else i=Int[1] =>
    Int[0]->Int[0].x + Int[1]->Int[2].x
  else
    Int[0]->Int[0].x + Int[1]->Int[1].x
  // Somehow I couldn't make the following work:
  // { j:Int, b:Bucket | ((int j)<(int i) && b=j.x) || ((int j)>=(int i) && b=Int[(int j)+1].x) }
}

fun append [x:Int->Bucket, b:Bucket] : Int->Bucket { x+Int[#x]->b }

