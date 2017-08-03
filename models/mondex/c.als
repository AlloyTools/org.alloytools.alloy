module mondex/c
open mondex/common as mondexCOMMON
open util/ordering[SEQNO] as seqord

sig SEQNO  {}

-- concrete signature for the state. Will be extended by the ConWorld signature
-- in order to show that individual purse operations are independent on
-- the ConWorld global variables.

sig ConState {}

-- We have to separately define Lt, Le, Gt, Ge in order to enforce the sets of SEQNO to be compared
-- to have exactly one element. Indeed, fields such as nextSeqNo are left unconstrained even as regards
-- multiplicity.

pred Lt (a, b : set SEQNO) {
    one a
    one b
    seqord/lt [a, b]
}

pred Le (a, b : set SEQNO) {
    one a
    one b
    seqord/lte [a, b]
}

pred Gt (a, b : set SEQNO) {
    one a
    one b
    seqord/gt [a, b]
}

pred Ge (a, b : set SEQNO) {
    one a
    one b
    seqord/gte [a, b]
}

sig PayDetails extends TransferDetails {
    fromSeqNo, toSeqNo : SEQNO
}

abstract sig STATUS {}
one sig eaFrom, epr, epv, epa extends STATUS {}
-- eaTo is useless, actually unused

-- ConPurse is a subset of NAME with concrete members. Indeed, identities of abstract and concrete
-- purses are common. This also implies that ConPurse does not extend Purse but is a subset, in order
-- to allow purses being both Abstract and Concrete.
-- So why not extend ConPurse directly from AbPurse, then ? Simply to show that Concrete properties are
-- independent on Abstract ones.

sig ConPurse in Purse {
    balance : Coin -> ConState,
    exLog : PayDetails -> ConState,
    nextSeqNo : SEQNO -> ConState,
    pdAuth : PayDetails -> ConState,
    status : STATUS -> ConState
}

pred XiConPurse (s, s' : ConState, a : set ConPurse) {
    a <: balance.s = a <: balance.s'
    a <: exLog.s = a <: exLog.s'
    a <: nextSeqNo.s = a <: nextSeqNo.s'
    a <: pdAuth.s = a <: pdAuth.s'
    a <: status.s = a <: status.s'
}

pred LogIfNecessary (s, s' : ConState, p : ConPurse) {
    p.exLog.s' = p.exLog.s + (some p.status.s & (epv + epa) => p.pdAuth.s else none)
}

pred XiConPurseIncrease (s, s' : ConState, p : ConPurse) {
    p.balance.s = p.balance.s'
    p.exLog.s = p.exLog.s'
    p.pdAuth.s = p.pdAuth.s'
    p.status.s = p.status.s'
}

pred IncreasePurseOkay (s, s' : ConState, p : ConPurse, m_out : MESSAGE) {
    XiConPurseIncrease [s, s', p]
    Ge [p.nextSeqNo.s', p.nextSeqNo.s]
    m_out = bottom
}

pred XiConPurseAbort (s, s' : ConState, p : ConPurse) {
    p.balance.s = p.balance.s'
}

pred AbortPurseOkay (s, s' : ConState, p : ConPurse) {
    p.status.s' = eaFrom
    Ge [p.nextSeqNo.s', p.nextSeqNo.s]
    XiConPurseAbort [s, s', p]
    LogIfNecessary [s, s', p]
}

abstract sig MESSAGE {}

abstract sig CounterPartyDetails extends MESSAGE {
    counterParty : ConPurse,
    value : set Coin,
    next : SEQNO
}

sig startFrom, startTo extends CounterPartyDetails {}

sig req extends MESSAGE {details : PayDetails}
sig val extends MESSAGE {details : PayDetails}
sig ack extends MESSAGE {details : PayDetails}

one sig readExceptionLog extends MESSAGE {}

sig exceptionLogResult extends MESSAGE {
    name : ConPurse,
    details : PayDetails
}

-- we do not use CLEAR codes any more
-- directly use sets of PayDetails
-- NOTE : one could also consider that the CLEAR code
-- and the exceptionLogClear message are the same thing.

sig exceptionLogClear extends MESSAGE {
    name : ConPurse,
    pds : set PayDetails
}

one sig bottom extends MESSAGE {}

pred XiConPurseStart (s, s' : ConState, p : ConPurse) {
    p.balance.s' = p.balance.s
    p.exLog.s' = p.exLog.s
}

pred ValidStartFrom (s : ConState, p : ConPurse, m : MESSAGE) {
    m in startFrom
    no m.counterParty & p
    m.value in p.balance.s
}

pred StartFromPurseEafromOkay (s, s' : ConState, p : ConPurse, m_in, m_out : MESSAGE) {
    ValidStartFrom [s, p, m_in]
    p.status.s = eaFrom
    XiConPurseStart [s, s', p]
    Gt [p.nextSeqNo.s', p.nextSeqNo.s]
    one p.pdAuth.s' -- ADDED
    p.pdAuth.s'.from = p
    p.pdAuth.s'.to = m_in.counterParty
    p.pdAuth.s'.value = m_in.value
    p.pdAuth.s'.fromSeqNo = p.nextSeqNo.s
    p.pdAuth.s'.toSeqNo = m_in.next
    p.status.s' = epr
    m_out = bottom
}

pred StartFromPurseOkay (s, s' : ConState, p : ConPurse, m_in, m_out : MESSAGE) {
    some s'' : ConState {
        AbortPurseOkay [s, s'', p]
        StartFromPurseEafromOkay [s'', s', p, m_in, m_out]
    }
}

pred ValidStartTo (s : ConState, p : ConPurse, m : MESSAGE) {
    m in startTo
    no m.counterParty & p

    -- added constraint : a coin in the transaction
    -- must not be already in the target balance
    -- TO BE TESTED
    no m.value & p.balance.s
}

pred StartToPurseEafromOkay (s, s' : ConState, p : ConPurse, m_in, m_out : MESSAGE) {
    ValidStartTo [s, p, m_in]
    p.status.s = eaFrom
    XiConPurseStart [s, s', p]
    Gt [p.nextSeqNo.s', p.nextSeqNo.s]
    one p.pdAuth.s' -- ADDED
    p.pdAuth.s'.from = m_in.counterParty
    p.pdAuth.s'.to = p
    p.pdAuth.s'.value = m_in.value
    p.pdAuth.s'.fromSeqNo = m_in.next
    p.pdAuth.s'.toSeqNo = p.nextSeqNo.s
    p.status.s' = epv
    m_out in req
    m_out.(req <: details) = p.pdAuth.s'
}

pred StartToPurseOkay (s, s' : ConState, p : ConPurse, m_in, m_out : MESSAGE) {
    some s'' : ConState {
        AbortPurseOkay [s, s'', p]
        StartToPurseEafromOkay [s'', s', p, m_in, m_out]
    }
}

pred XiConPurseReq (s, s' : ConState, a : ConPurse) {
    a.exLog.s = a.exLog.s'
    a.nextSeqNo.s = a.nextSeqNo.s'
    a.pdAuth.s = a.pdAuth.s'
}

pred AuthenticReqMessage (s : ConState, p : ConPurse, m : MESSAGE) {
    m in req
    m.(req <: details) = p.pdAuth.s
}

pred ReqPurseOkay (s, s' : ConState, p : ConPurse, m_in, m_out : MESSAGE) {
    AuthenticReqMessage [s, p, m_in]
    p.status.s = epr
    XiConPurseReq [s, s', p]
    p.balance.s' = p.balance.s - p.pdAuth.s.value
    p.status.s' = epa
    m_out in val
    m_out.(val <: details) = p.pdAuth.s
}

pred XiConPurseVal (s, s' : ConState, a : ConPurse) {
    a.exLog.s = a.exLog.s'
    a.nextSeqNo.s = a.nextSeqNo.s'
    a.pdAuth.s = a.pdAuth.s'
}

pred AuthenticValMessage (s : ConState, p : ConPurse, m : MESSAGE) {
    m in val
    m.(val <: details) = p.pdAuth.s
}

pred ValPurseOkay (s, s' : ConState, p : ConPurse, m_in, m_out : MESSAGE) {
    AuthenticValMessage [s, p, m_in]
    p.status.s = epv
    XiConPurseVal [s, s', p]
    p.balance.s' = p.balance.s + p.pdAuth.s.value
    p.status.s' = eaFrom -- formerly eaTo but not used
    m_out in ack
    m_out.(ack <: details) = p.pdAuth.s
}

pred XiConPurseAck (s, s' : ConState, a : ConPurse) {
    a.exLog.s = a.exLog.s'
    a.nextSeqNo.s = a.nextSeqNo.s'
    a.balance.s = a.balance.s'
}

pred AuthenticAckMessage (s : ConState, p : ConPurse, m : MESSAGE) {
    m in ack
    m.(ack <: details) = p.pdAuth.s
}

pred AckPurseOkay (s, s' : ConState, p : ConPurse, m_in, m_out : MESSAGE) {
    AuthenticAckMessage [s, p, m_in]
    p.status.s = epa
    XiConPurseAck [s, s', p]
    p.status.s' = eaFrom
    m_out = bottom
}


pred ReadExceptionLogPurseEafromOkay (s, s' : ConState, p : ConPurse, m_in, m_out : MESSAGE) {
    XiConPurse [s, s', p]
    m_in = readExceptionLog
    p.status.s = eaFrom
    m_out in bottom + exceptionLogResult
    m_out in exceptionLogResult implies {
        m_out.(exceptionLogResult <: name) = p
                m_out.(exceptionLogResult <: details) in p.exLog.s
    }
}

pred ReadExceptionLogPurseOkay (s, s' : ConState, p : ConPurse, m_in, m_out : MESSAGE) {
    some s'' : ConState {
        AbortPurseOkay [s, s'', p]
        ReadExceptionLogPurseEafromOkay [s'', s', p, m_in, m_out]
    }
}

pred XiConPurseClear (s, s' : ConState, a : ConPurse) {
    a.balance.s = a.balance.s'
    a.nextSeqNo.s = a.nextSeqNo.s'
    a.pdAuth.s = a.pdAuth.s'
    a.status.s = a.status.s'
}

pred ClearExceptionLogPurseEafromOkay (s, s' : ConState, p : ConPurse, m_in, m_out : MESSAGE) {
    some p.exLog.s
    m_in in exceptionLogClear
    m_in.(exceptionLogClear <: name) = p
    m_in.pds = p.exLog.s
    p.status.s = eaFrom
    XiConPurseClear [s, s', p]
    no p.exLog.s'
    m_out = bottom
}

pred ClearExceptionLogPurseOkay (s, s' : ConState, p : ConPurse, m_in, m_out : MESSAGE) {
    some s'' : ConState {
        AbortPurseOkay [s, s'', p]
        ClearExceptionLogPurseEafromOkay [s'', s', p, m_in, m_out]
    }
}
