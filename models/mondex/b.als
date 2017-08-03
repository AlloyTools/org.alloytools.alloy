module mondex/b
open mondex/cw as mondexCW
open mondex/c  as mondexC
open mondex/common as mondexCOMMON

fun allLogs (c : ConWorld) : ConPurse -> PayDetails {
    c.archive + (c.conAuthPurse <: exLog.c)
}

fun authenticFrom (c : ConWorld) : set TransferDetails {
    from.(c.conAuthPurse)
}

fun authenticTo (c : ConWorld) : set TransferDetails {
    to.(c.conAuthPurse)
}

fun fromLogged (c : ConWorld) : set PayDetails {
    authenticFrom [c] & ConPurse.(allLogs [c] & ~from)
}

fun toLogged (c : ConWorld) : set PayDetails {
    authenticTo [c] & ConPurse.(allLogs [c] & ~to)
}

fun toInEpv (c : ConWorld) : set TransferDetails {
    authenticTo [c] & to.status.c.epv & (iden & to.(pdAuth.c)).PayDetails
}

fun fromInEpr (c : ConWorld) : set TransferDetails {
    authenticFrom [c] & from.status.c.epr & (iden & from.(pdAuth.c)).PayDetails
}

fun fromInEpa (c : ConWorld) : set TransferDetails {
    authenticFrom [c] & from.status.c.epa & (iden & from.(pdAuth.c)).PayDetails
}

fun definitelyLost (c : ConWorld) : set PayDetails {
    toLogged [c] & (fromLogged [c] + fromInEpa [c])
}

fun maybeLost (c : ConWorld) : set TransferDetails {
    (fromInEpa [c] + fromLogged [c]) & toInEpv [c]
}

assert auxworld_identity {
    all c : ConWorld | Concrete [c] implies
    definitelyLost [c] + maybeLost [c] = (fromInEpa [c] + fromLogged [c]) & (toInEpv [c] + toLogged [c])
}

check auxworld_identity for 6

pred Between1 (c : ConWorld) {
    (c.ether & req).details in authenticTo [c]
}

pred Between2 (c : ConWorld) {
    all r : req | r in c.ether implies Lt [r.details.toSeqNo, r.details.to.nextSeqNo.c]
}

pred Between3 (c : ConWorld) {
    all v : val | v in c.ether implies {
        Lt [v.details.toSeqNo, v.details.to.nextSeqNo.c]
        Lt [v.details.fromSeqNo, v.details.from.nextSeqNo.c]
    }
}

pred Between4 (c : ConWorld) {
    all v : ack | v in c.ether implies {
        Lt [v.details.toSeqNo, v.details.to.nextSeqNo.c]
        Lt [v.details.fromSeqNo, v.details.from.nextSeqNo.c]
    }
}

pred Between5 (c : ConWorld) {
    all p : PayDetails | p in fromLogged [c] implies Lt [p.fromSeqNo, p.from.nextSeqNo.c]
}

pred Between6 (c : ConWorld) {
    all p : PayDetails | p in toLogged [c] implies Lt [p.toSeqNo, p.to.nextSeqNo.c]
}

pred Between7 (c : ConWorld) {
    all p : PayDetails | {
        p in fromLogged [c]
        p.from.status.c in epr + epa
    } implies Lt [p.fromSeqNo, p.from.pdAuth.c.fromSeqNo]
}

pred Between8 (c : ConWorld) {
    all p : PayDetails | {
        p in toLogged [c]
        p.to.status.c in epv
    } implies Lt [p.toSeqNo, p.to.pdAuth.c.toSeqNo]
}

pred Between9 (c : ConWorld) {
    no c.ether.(val <: details + ack <: details) & fromInEpr [c]
}

pred Between10 (c : ConWorld) {
--  all p : PayDetails | {
--      some c.ether & (req <: details.p)
--      no c.ether & (ack <: details.p)
--  } iff
--  p in toInEpv [c] + toLogged [c]

    toInEpv [c] + toLogged [c] = c.ether.(req <: details) - c.ether.(ack <: details)
}

pred Between11 (c : ConWorld) {
    c.ether.(val <: details) & toInEpv [c] in fromInEpa [c] + fromLogged [c]
}

pred Between12 (c : ConWorld) {
    fromInEpa [c] + fromLogged [c] in c.ether.(req <: details)
}

pred Between13 (c : ConWorld) {
-- IGNORED : toLogged finite
}

pred Between14 (c : ConWorld) {
    ~((c.ether & exceptionLogResult) <: name).details in allLogs [c]
}

pred Between15 (c : ConWorld) {
    ~((c.ether & exceptionLogClear) <: name).pds in c.archive
}

pred Between16 (c : ConWorld) {
    fromLogged [c] + toLogged [c] in c.ether.(req <: details)
}

pred Between_MISSING (c : ConWorld) {
    -- authenticity of pdAuth hold by an epv purse
    ((c.conAuthPurse & status.c.epv) <: pdAuth.c.to) + ((c.conAuthPurse & status.c.epa) <: pdAuth.c.from) in iden

    -- authenticity of val and ack messages
    c.ether.(val <: details + ack <: details).(from + to) in c.conAuthPurse

    -- bottom in ether (needed to consider compositions for operations that first abort)
    bottom in c.ether
}

-- Contrary to multiplicity issues, which are part of the original specification and added as predicates
-- rather than enforced in the ConWorld definition, Coin sharing issues are due to the choice of the
-- representation of the amounts, which is a data issue, hence consisting in a change from the original
-- spec which used to use integers.

pred Between_Coin (s : ConWorld) {
    -- coin sharing

    -- Purses cannot log money still in their balances
    -- i.e. a balance coin cannot be logged lost
    -- either in the local (exLog) or global (archive) lost journal
    -- Those constraints appear to be too strong
--  no s.conAuthPurse.(exLog.s.value & balance.s)
--  no s.conAuthPurse.balance.s & s.conAuthPurse.(s.archive).value
    -- Yes, but I have something to express that.
    no s.conAuthPurse.balance.s & (definitelyLost[s] + maybeLost[s]).value

    -- Purses have their own balances
    -- i.e. a coin cannot be owned by different purse balances
    s.conAuthPurse <: balance.s in ConPurse lone -> Coin

    -- A purse in epv cannot receive its own money
    -- i.e. a coin cannot be received twice into balance
    no (s.conAuthPurse & status.s.epv).(pdAuth.s.value & balance.s)

    -- The values of transfers maybe lost are disjoint
    -- i.e. a coin cannot be lost twice
    (maybeLost [s] + definitelyLost [s]) <: value in PayDetails lone -> Coin

}

-- Here are the original constraints (proper to the Between world, additional to the Concrete)

pred Between0 (c : ConWorld) {
    Between1 [c]
    Between2 [c]
    Between3 [c]
    Between4 [c]
    Between5 [c]
    Between6 [c]
    Between7 [c]
    Between8 [c]
    Between9 [c]
    Between10 [c]
    Between11 [c]
    Between12 [c]
    Between13 [c]
    Between14 [c]
    Between15 [c]
    Between16 [c]
}

-- They are summed up with added constraints :
-- missing ones (lack in the Z spec)
-- coin sharing (added due to spec change)
-- BUT NOT multiplicity (language issue)

pred Between (c : ConWorld) {
    Concrete [c]
    Between0 [c]
    Between_MISSING [c]
    Between_Coin [c]
}
