module appendixA/prison

sig Gang { members: set Inmate }

sig Inmate { room: Cell }

sig Cell { }

pred safe {
	// your constraints should go here
	}

pred show {
	// your constraints should go here
	}

run show
