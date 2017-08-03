module mondex/cop
open mondex/cw as mondexCW
open mondex/c as mondexC
open mondex/common as mondexCOMMON

-- 2006-07-12 DONE

pred COp (s, s' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    m_in in s.ether
    p in s.conAuthPurse
    s'.conAuthPurse = s.conAuthPurse
    XiConPurse [s, s', s.conAuthPurse - p]
    s'.archive = s.archive
    s'.ether in s.ether + m_out
}

pred CIgnore (s, s' : ConWorld, m_out : MESSAGE) {
    s'.conAuthPurse = s.conAuthPurse
    XiConPurse [s, s', s.conAuthPurse]
    s'.archive = s.archive
    s'.ether = s.ether
    m_out = bottom
}

pred CIncrease (s, s' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    CIgnore [s, s', m_out] or {
        COp [s, s', p, m_in, m_out]
        IncreasePurseOkay [s, s', p, m_out]
    }
}

pred CAbort (s, s' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    CIgnore [s, s', m_out] or {
        COp [s, s', p, m_in, m_out]
        AbortPurseOkay [s, s', p]
        m_out = bottom
    }
}

pred CStartFrom (s, s' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    CIgnore [s, s', m_out] or CAbort [s, s', p, m_in, m_out] or {
        COp [s, s', p, m_in, m_out]
        StartFromPurseOkay [s, s', p, m_in, m_out]
    }
}

pred CStartTo (s, s' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    CIgnore [s, s', m_out] or CAbort [s, s', p, m_in, m_out] or {
        COp [s, s', p, m_in, m_out]
        StartToPurseOkay [s, s', p, m_in, m_out]
    }
}

pred CReq (s, s' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    CIgnore [s, s', m_out] or {
        COp [s, s', p, m_in, m_out]
        ReqPurseOkay [s, s', p, m_in, m_out]
    }
}

pred CVal (s, s' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    CIgnore [s, s', m_out] or {
        COp [s, s', p, m_in, m_out]
        ValPurseOkay [s, s', p, m_in, m_out]
    }
}

pred CAck (s, s' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    CIgnore [s, s', m_out] or {
        COp [s, s', p, m_in, m_out]
        AckPurseOkay [s, s', p, m_in, m_out]
    }
}

pred CReadExceptionLog (s, s' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    CIgnore [s, s', m_out] or CAbort [s, s', p, m_in, m_out] or {
        COp [s, s', p, m_in, m_out]
        ReadExceptionLogPurseOkay [s, s', p, m_in, m_out]
    }
}

pred CClearExceptionLog (s, s' :ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    CIgnore [s, s', m_out] or CAbort [s, s', p, m_in, m_out] or {
        COp [s, s', p, m_in, m_out]
        ClearExceptionLogPurseOkay [s, s', p, m_in, m_out]
    }
}

pred CAuthorizeExLogClearOkay (s, s' : ConWorld, p : ConPurse, m_out : MESSAGE) {
    XiConPurse [s, s', p]
    m_out in exceptionLogClear
    ~(m_out <: name).pds in s.archive
    m_out.(exceptionLogClear <: name) = p
}

pred CAuthorizeExLogClear (s, s' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    CIgnore [s, s', m_out] or {
        COp [s, s', p, m_in, m_out]
        CAuthorizeExLogClearOkay [s, s', p, m_out]
    }
}

pred CArchive (s, s' : ConWorld, m_out : MESSAGE) {
    s'.conAuthPurse = s.conAuthPurse
    XiConPurse [s, s', s.conAuthPurse]
    s'.ether in s.ether

    s.archive in s'.archive
    s'.archive in s.archive + ~(s.ether <: name).details
    m_out = bottom
}

-- model consistency

-- totality
assert CTotal {
    all c : ConWorld, m_in : MESSAGE, p : ConPurse | Concrete [c] implies {
        CIgnore [c, c, bottom]
        CIncrease [c, c, p, m_in, bottom]
        CAbort [c, c, p, m_in, bottom]
        CStartFrom [c, c, p, m_in, bottom]
        CStartTo [c, c, p, m_in, bottom]
        CReq [c, c, p, m_in, bottom]
        CVal [c, c, p, m_in, bottom]
        CAck [c, c, p, m_in, bottom]
        CReadExceptionLog [c, c, p, m_in, bottom]
        CClearExceptionLog [c, c, p, m_in, bottom]
        CAuthorizeExLogClear [c, c, p, m_in, bottom]
        CArchive [c, c, bottom]
    }
}

check CTotal for 10 -- 0:57 (minisat)
