module mondex/bcif

-- Between and Concrete world : initialization and finalization

open mondex/b as mondexB
open mondex/cw as mondexCW
open mondex/c as mondexC
open mondex/a as mondexA
open mondex/common as mondexCOMMON

pred BetwInitState (s : ConWorld) {
--  bottom +  -- moved to BetweenWorld MISSING constraints
    Between [s]
    readExceptionLog + startFrom + startTo in s.ether
}

pred ConInitState (c : ConWorld) {
    Concrete [c]
    some b : ConWorld {
        BetwInitState [b]
        c.conAuthPurse = b.conAuthPurse
        XiConPurse [c, b, c.conAuthPurse]
        c.archive = b.archive
        c.ether in b.ether
--  TO BE TESTED : remove this constraint (C ether is completely lossy)
--      bottom in c.ether
    }
}

pred InitIn (g : AIN, m : MESSAGE) {
    m in req implies {
        g in TransferDetails
        XiTransfer [g, m.(req <: details)]
    }
}

pred FinState (b : ConWorld, g : AbWorld) {
    g.abAuthPurse = b.conAuthPurse
    g.abAuthPurse <: abBalance.g = b.conAuthPurse <: balance.b
    g.abAuthPurse <: abLost.g = ((b.conAuthPurse->(definitelyLost [b] + maybeLost [b])) & ~from).value
}

pred FinOut (g : AOUT) {
    g = aNullOut
}

pred simul () {
    some c : ConWorld {
        ConInitState [c]
        -- some c.ether & val -- gives a weird but valid example, how to comment on it ?
        some c.conAuthPurse.status.c & epv
    }
}

run BetwInitState for 10 but 1 ConState
run ConInitState for 10 but 2 ConState
run simul for 10 but 2 ConState --
-- run simul for 10 but 1 ConState, 2 ConWorld -- impossible because "1 ConState" defines
-- scope for whole ConState including ConWorld.
