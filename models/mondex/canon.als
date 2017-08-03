module mondex/canon
open mondex/a as mondexA
open mondex/cw as mondexCW
open mondex/c as mondexC
open mondex/common as mondexCOMMON

-- Canonicalization facts to be optionally added in order to
-- eventually make checkings faster.

fact ax_AbWorld_canon {
    no a1, a2 : AbWorld {
        no (a1&a2)
        a1.abAuthPurse = a2.abAuthPurse
        XiAbPurse [a1, a2, a1.abAuthPurse]
    }
}

fact ax_PayDetails_canon {
    from.~from & to.~to & fromSeqNo.~fromSeqNo & toSeqNo.~toSeqNo in iden
}

fact ax_ConWorld_canon {
    no c1, c2 : ConWorld {
        no (c1&c2)
        c1.conAuthPurse = c2.conAuthPurse
        XiConPurse [c1, c2, c1.conAuthPurse]
        c1.ether = c2.ether
        c1.archive = c2.archive
    }
}
