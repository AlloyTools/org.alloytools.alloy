module mondex/bop
open mondex/cw as mondexCW
open mondex/c as mondexC
open mondex/common as mondexCOMMON

pred BOp (s, s' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    m_in in s.ether
    p in s.conAuthPurse
    s'.conAuthPurse = s.conAuthPurse
    XiConPurse [s, s', s.conAuthPurse - p]
    s'.archive = s.archive
    s'.ether = s.ether + m_out
}

pred Ignore (s, s' : ConWorld, m_out : MESSAGE) {
    s'.conAuthPurse = s.conAuthPurse
    XiConPurse [s, s', s.conAuthPurse]
    s'.archive = s.archive
    s'.ether = s.ether
}

pred IncreaseOkay (s, s' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    BOp [s, s', p, m_in, m_out]
    IncreasePurseOkay [s, s', p, m_out]
}

pred Increase (s, s' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    Ignore [s, s', m_out] or IncreaseOkay [s, s', p, m_in, m_out]
}

pred AbortOkay (s, s' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    BOp [s, s', p, m_in, m_out]
    AbortPurseOkay [s, s', p]
    m_out = bottom
}

pred Abort (s, s' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    Ignore [s, s', m_out] or AbortOkay [s, s', p, m_in, m_out]
}

pred StartFrom (s, s' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    Ignore [s, s', m_out] or Abort [s, s', p, m_in, m_out] or {
        BOp [s, s', p, m_in, m_out]
        StartFromPurseOkay [s, s', p, m_in, m_out]
        -- ADDED : PayDetails canonicalization (because this operation creates a PayDetails
        -- which may exist before)
        PayDetails_canon [s']
    }
}

pred StartFromEafrom (s, s' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    BOp [s, s', p, m_in, m_out]
    StartFromPurseEafromOkay [s, s', p, m_in, m_out]
    PayDetails_canon [s'] -- ADDED
}

pred StartTo (s, s' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    Ignore [s, s', m_out] or Abort [s, s', p, m_in, m_out] or {
        BOp [s, s', p, m_in, m_out]
        StartToPurseOkay [s, s', p, m_in, m_out]
        PayDetails_canon [s'] -- ADDED
    }
}

pred StartToEafrom (s, s' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    BOp [s, s', p, m_in, m_out]
    StartToPurseEafromOkay [s, s', p, m_in, m_out]
    PayDetails_canon [s'] -- ADDED
}

pred ReqOkay (s, s' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    BOp [s, s', p, m_in, m_out]
    ReqPurseOkay [s, s', p, m_in, m_out]
}

pred Req (s, s' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    Ignore [s, s', m_out] or ReqOkay [s, s', p, m_in, m_out]
}

pred ValOkay (s, s' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    BOp [s, s', p, m_in, m_out]
    ValPurseOkay [s, s', p, m_in, m_out]
}

pred Val (s, s' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    Ignore [s, s', m_out] or ValOkay [s, s', p, m_in, m_out]
}

pred AckOkay (s, s' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    BOp [s, s', p, m_in, m_out]
    AckPurseOkay [s, s', p, m_in, m_out]
}

pred Ack (s, s' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    Ignore [s, s', m_out] or AckOkay [s, s', p, m_in, m_out]
}

pred ReadExceptionLog (s, s' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    Ignore [s, s', m_out] or Abort [s, s', p, m_in, m_out] or {
        BOp [s, s', p, m_in, m_out]
        ReadExceptionLogPurseOkay [s, s', p, m_in, m_out]
    }
}

pred ReadExceptionLogEafrom (s, s' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    BOp [s, s', p, m_in, m_out]
    ReadExceptionLogPurseEafromOkay [s, s', p, m_in, m_out]
}

pred ClearExceptionLog (s, s' :ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    Ignore [s, s', m_out] or Abort [s, s', p, m_in, m_out] or {
        BOp [s, s', p, m_in, m_out]
        ClearExceptionLogPurseOkay [s, s', p, m_in, m_out]
    }
}

pred ClearExceptionLogEafrom (s, s' :ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    BOp [s, s', p, m_in, m_out]
    ClearExceptionLogPurseEafromOkay [s, s', p, m_in, m_out]
}

pred AuthorizeExLogClearOkay (s, s' : ConWorld, p : ConPurse, m_out : MESSAGE) {
    s'.conAuthPurse = s.conAuthPurse
    XiConPurse [s, s', s.conAuthPurse]
    m_out in exceptionLogClear
    ~(m_out <: name).pds in s.archive
    m_out.(exceptionLogClear <: name) = p
    s'.ether = s.ether + m_out
    s'.archive = s.archive
}

pred AuthorizeExLogClear (s, s' : ConWorld, p : ConPurse, m_out : MESSAGE) {
    Ignore [s, s', m_out] or AuthorizeExLogClearOkay [s, s', p, m_out]
}

pred Archive (s, s' : ConWorld, m_out : MESSAGE) {
    s'.conAuthPurse = s.conAuthPurse
    XiConPurse [s, s', s.conAuthPurse]
    s'.ether = s.ether
    s.archive in s'.archive
    s'.archive in s.archive + ~(s.ether <: name).details
    m_out = bottom
}
