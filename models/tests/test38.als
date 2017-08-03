module tests/test

// open util/seqrel[B] as sq

abstract sig B {}
one sig B1,B2,B3,B4,B5 extends B {}

fact { some S1,S2,S3,T1,T2,T3,T4:seq B | {


#S1=1
#S2=2
#rest[S3]=2
#elems[S3]=2
#butlast[S3]=2
first[S3] != last[S1]
hasDups[S3]
lastIdx[S1] != lastIdx[S3]
afterLastIdx[S1] in inds[S3]
some idxOf[S3, B2]
no lastIdxOf[S3, B3]
some indsOf[S3, B2]
S3=S2.add[B5]
T1=S1.insert[0,B1]
T2=T1.delete[0]
T3=T1.append[T2]
T4=T3.subseq[1,2]
}}

run {} for 3 int, 3 seq, exactly 5 B expect 1
