sig Value {}

sig Buffer {
	succ : one Buffer,
	var content : lone Value
}

var one sig read, write in Buffer {}

fact circular {
	all b : Buffer | Buffer in b.^succ
}

fact init {
	read = write
	no content
}

pred send [v : Value] {
	no write.content

	content' = content + write -> v
	write' = write.succ
	read' = read	
}

pred receive [v : Value] {
	some read.content
	v = read.content

	content' = content - read -> v
	write' = write
	read' = read.succ
}

pred stutter {
	content' = content
	write' = write
	read' = read
}

fact transitions {
	always (stutter or some v : Value | send[v] or receive[v])
}

run {}

assert everyReceivedValueWasSent {
	all v : Value | always (receive[v] implies once send[v])
}
check everyReceivedValueWasSent for 4

assert orderIsPreserved {
	all x, y : Value | always ((receive[x] and once receive[y]) implies once (send[x] and once send[y]))
}

check orderIsPreserved for 3

pred receiveEnabled[v : Value] {
	some read.content
	read.content = v
}

pred receiveWeakFairness { all v : Value |
	(eventually always receiveEnabled[v]) implies 
	(always eventually receive[v])
}

run receiveWeakFairness

assert everySentValueWillBeReceived {
	receiveWeakFairness implies 
	all v : Value | always (send[v] implies eventually receive[v])
} 
check everySentValueWillBeReceived for 3
