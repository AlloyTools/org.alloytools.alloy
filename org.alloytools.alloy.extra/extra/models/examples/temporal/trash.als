var sig File {}
var sig Trash in File {}

pred delete [f: File] {
	f not in Trash
	Trash' = Trash + f
	File' = File
}

pred restore [f: File] {
	f in Trash
	Trash' = Trash - f
	File' = File
}

pred empty {
	some Trash
	no Trash'
	File' = File - Trash
}

pred do_nothing {
	File' = File
	Trash' = Trash
}

pred restoreEnabled [f:File] {
  f in Trash
}

fact Behaviour {
	no Trash
	always {
//		(some f: File | delete[f] or restore[f]) or empty
		(some f: File | delete[f] or restore[f]) or empty or do_nothing
	}
} 

example: run {}

assert restoreAfterDelete {
	always (all f : File | restore[f] implies once delete[f])
}

check restoreAfterDelete for 10 steps
check restoreAfterDelete for 1.. steps

assert deleteAll {
//	always ((File in Trash and empty) implies always no File)
	always ((File in Trash and empty) implies after always no File)
}

check deleteAll

check Exercise1 {
	-- The set of files never increases
	always (File' in File)
}


check Exercise2 {
	-- The set of files only changes when empty is performed
	always (File' != File implies empty)
}

check Exercise3 {
  (always all f : File | not delete[f]) implies always not empty
}

check Exercise4 {
	-- Once you have no files you never have files again
	always (no File implies always no File)
}

assert restoreIsPossibleBeforeEmpty {
  --  a deleted file can still be restored if the trash is not emptied
  --  always (all f:File | delete[f] implies (empty releases restoreEnabled[f]))
  --  always (all f:File | delete[f] implies ((empty or restore[f]) releases restoreEnabled[f]))
  always (all f:File | delete[f] implies after ((empty or restore[f]) releases restoreEnabled[f]))
}

check restoreIsPossibleBeforeEmpty for 3 but 1.. steps
