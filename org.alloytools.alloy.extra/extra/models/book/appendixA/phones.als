module appendixA/phones

sig Phone {
	requests: set Phone,
	connects: lone Phone
	}
