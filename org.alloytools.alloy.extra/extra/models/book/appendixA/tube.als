module appendixA/tube

abstract sig Station {
	jubilee, central, circle: set Station
	}

sig Jubilee, Central, Circle in Station {}

one sig
	Stanmore, BakerStreet, BondStreet, Westminster, Waterloo,
	WestRuislip, EalingBroadway, NorthActon, NottingHillGate,
	LiverpoolStreet, Epping
	extends Station {}

fact {
	// the constraints should go here
	}

pred show {}

run show
