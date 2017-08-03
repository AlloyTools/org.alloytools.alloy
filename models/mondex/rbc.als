module mondex/rbc
open mondex/bop as mondexBOP
open mondex/b as mondexB
open mondex/cop as mondexCOP
open mondex/cw as mondexCW
open mondex/c as mondexC
open mondex/common as mondexCOMMON

-- 2006-07-13 DONE with scopes 10 (eventually limited ConState scopes)

-- for final state
open mondex/bcif as mondexBCIF
open mondex/a as mondexA

-- This module is less important than the equivalent Rbc module
-- of the former model. Indeed, here the proof schema is
-- Rbc /\ Rbc' /\ COp /\ Concrete /\ Concrete' /\ Between => BOp,
-- so nothing about Between'.
-- In fact, in the bopc module is conducted the proof schema
-- Between /\ BOp => Between'
-- which completes the Rbc refinement.

pred Rbc (b, c : ConWorld) {
    b.conAuthPurse = c.conAuthPurse
    XiConPurse [b, c, b.conAuthPurse]
    c.ether in b.ether
    b.archive = c.archive
}

pred Rbc_constr (b', c' : ConWorld, eth : set MESSAGE, m_out : MESSAGE) {
    b'.conAuthPurse = c'.conAuthPurse
    XiConPurse [b', c', b'.conAuthPurse]
    b'.ether = eth + m_out
    b'.archive = c'.archive
}

assert Rbc_init {
    all c : ConWorld |
    ConInitState [c] implies (some b : ConWorld { Rbc [b, c] && BetwInitState [b] })
}

check Rbc_init for 10 but 2 ConState -- 10007s (siege_v4) -- 10 : aborted by user after 7h computation (minisat)

assert Rbc_fin {
    all g : AbWorld, b, c : ConWorld | {
        FinState [c, g]
        Rbc [b, c]
        Concrete [c]
        Between [b]
    } implies FinState [b, g]
}

check Rbc_fin for 10 but 2 ConState, 1 AbWorld -- 841s (siege_v4)

assert Rbc_ignore {
    all b, b', c, c' : ConWorld, m_out : MESSAGE | {
        Between [b]
        Concrete [c]
        Concrete [c']
        Rbc [b, c]
        Rbc_constr [b', c', b.ether, m_out]
        CIgnore [c, c', m_out]
    } implies {
        Rbc [b', c']
        Ignore [b, b', m_out]
    }
}

check Rbc_ignore for 10 -- 1:26 (minisat)

assert Rbc_increase {
    all b, b', c, c' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE | {
        Between [b]
        Concrete [c]
        Concrete [c']
        Rbc [b, c]
        Rbc_constr [b', c', b.ether, m_out]
        CIncrease [c, c', p, m_in, m_out]
    } implies {
        Rbc [b', c']
        Increase [b, b', p, m_in, m_out]
    }
}

check Rbc_increase for 10 -- 2:32 (minisat)

assert Rbc_abort {
    all b, b', c, c' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE | {
        Between [b]
        Concrete [c]
        Concrete [c']
        Rbc [b, c]
        Rbc_constr [b', c', b.ether, m_out]
        CAbort [c, c', p, m_in, m_out]
    } implies {
        Rbc [b', c']
        Abort [b, b', p, m_in, m_out]
    }
}

check Rbc_abort for 10  -- 2:11 (minisat)

assert Rbc_startFrom {
    all b, b', c, c' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE | {
        Between [b]
        Concrete [c]
        Concrete [c']
        Rbc [b, c]
        Rbc_constr [b', c', b.ether, m_out]
        CStartFrom [c, c', p, m_in, m_out]
    } implies {
        Rbc [b', c']
        StartFrom [b, b', p, m_in, m_out]
    }
}

check Rbc_startFrom for 10 -- was formerly 3:15 (minisat)
-- but exploded due to PayDetails canonicalization constraint in StartFrom
-- so, we need to restrict ConState. We may say 5 ConStates : 2 Concrete, 2 Between,
-- and 1 intermediate are enough because we do not care about the ether/archive of the
-- intermediate state, properties which could even not exist.
check Rbc_startFrom for 10 but 5 ConState -- 12456s (siege_v4)

assert Rbc_startTo {
    all b, b', c, c' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE | {
        Between [b]
        Concrete [c]
        Concrete [c']
        Rbc [b, c]
        Rbc_constr [b', c', b.ether, m_out]
        CStartTo [c, c', p, m_in, m_out]
    } implies {
        Rbc [b', c']
        StartTo [b, b', p, m_in, m_out]
    }
}

check Rbc_startTo for 10 -- formerly 2:51 (minisat), exploded (cf. startFrom)
check Rbc_startTo for 10 but 5 ConState -- 6208s (siege_v4)

assert Rbc_req {
    all b, b', c, c' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE | {
        Between [b]
        Concrete [c]
        Concrete [c']
        Rbc [b, c]
        Rbc_constr [b', c', b.ether, m_out]
        CReq [c, c', p, m_in, m_out]
    } implies {
        Rbc [b', c']
        Req [b, b', p, m_in, m_out]
    }
}

check Rbc_req for 10 -- 2:18

assert Rbc_val {
    all b, b', c, c' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE | {
        Between [b]
        Concrete [c]
        Concrete [c']
        Rbc [b, c]
        Rbc_constr [b', c', b.ether, m_out]
        CVal [c, c', p, m_in, m_out]
    } implies {
        Rbc [b', c']
        Val [b, b', p, m_in, m_out]
    }
}

check Rbc_val for 10 -- 2:06

assert Rbc_ack {
    all b, b', c, c' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE | {
        Between [b]
        Concrete [c]
        Concrete [c']
        Rbc [b, c]
        Rbc_constr [b', c', b.ether, m_out]
        CAck [c, c', p, m_in, m_out]
    } implies {
        Rbc [b', c']
        Ack [b, b', p, m_in, m_out]
    }
}

check Rbc_ack for 10 -- 1:59

assert Rbc_readExceptionLog {
    all b, b', c, c' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE | {
        Between [b]
        Concrete [c]
        Concrete [c']
        Rbc [b, c]
        Rbc_constr [b', c', b.ether, m_out]
        CReadExceptionLog [c, c', p, m_in, m_out]
    } implies {
        Rbc [b', c']
        ReadExceptionLog [b, b', p, m_in, m_out]
    }
}

check Rbc_readExceptionLog for 10 -- 2:44

assert Rbc_clearExceptionLog {
    all b, b', c, c' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE | {
        Between [b]
        Concrete [c]
        Concrete [c']
        Rbc [b, c]
        Rbc_constr [b', c', b.ether, m_out]
        CClearExceptionLog [c, c', p, m_in, m_out]
    } implies {
        Rbc [b', c']
        ClearExceptionLog [b, b', p, m_in, m_out]
    }
}

check Rbc_clearExceptionLog for 10 -- 2:46

assert Rbc_authorizeExLogClear {
    all b, b', c, c' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE | {
        Between [b]
        Concrete [c]
        Concrete [c']
        Rbc [b, c]
        Rbc_constr [b', c', b.ether, m_out]
        CAuthorizeExLogClear [c, c', p, m_in, m_out]
    } implies {
        Rbc [b', c']
        AuthorizeExLogClear [b, b', p, m_out]
    }
}

check Rbc_authorizeExLogClear for 10 -- 1:56

assert Rbc_archive {
    all b, b', c, c' : ConWorld, m_out : MESSAGE | {
        Between [b]
        Concrete [c]
        Concrete [c']
        Rbc [b, c]
        Rbc_constr [b', c', b.ether, m_out]
        CArchive [c, c', m_out]
    } implies {
        Rbc [b', c']
        Archive [b, b', m_out]
    }
}

check Rbc_archive for 10 -- 1:53

