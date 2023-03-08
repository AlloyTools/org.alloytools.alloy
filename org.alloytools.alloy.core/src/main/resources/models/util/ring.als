module util/ring[exactly elem]
open util/ordering[elem] as order

fun nextRing [ie: elem] : lone elem  {
	{m: elem | no order/next[ie] implies m = order/first
		else m = order/next[ie]
	}
}
