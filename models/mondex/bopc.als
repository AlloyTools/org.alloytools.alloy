module mondex/bopc
open mondex/bop as mondexBOP
open mondex/b as mondexB
open mondex/cw as mondexCW
open mondex/c as mondexC
open mondex/common as mondexCOMMON

-- As in rab.als, you'll maybe want to canonicalize in order to
-- make checkings faster, won't you ?
open mondex/canon as mondexCANON

-- Between operations : model consistency

-- Totality
assert BOp_total {
    all b : ConWorld, m_in : MESSAGE, p : ConPurse | Between [b] implies {
        Ignore [b, b, bottom]
        Increase [b, b, p, m_in, bottom]
        Abort [b, b, p, m_in, bottom]
        StartFrom [b, b, p, m_in, bottom]
        StartTo [b, b, p, m_in, bottom]
        Req [b, b, p, m_in, bottom]
        Val [b, b, p, m_in, bottom]
        Ack [b, b, p, m_in, bottom]
        ReadExceptionLog [b, b, p, m_in, bottom]
        ClearExceptionLog [b, b, p, m_in, bottom]
        AuthorizeExLogClear [b, b, p, bottom]
        Archive [b, b, bottom]
    }
}

check BOp_total for 10 -- 3:47 (minisat)

-- More than that.
-- The schema morphology in the Z spec is ambiguous. Indeed, an operation
-- takes 2 BetweenWorld said to verify the Between constraints. But mostly,
-- Between' is *defined* by the operation, which makes me ask myself : do these
-- definitions always make the Between constraints hold ?
-- Let's directly attempt to show this on Between worlds, that is : let me consider Between
-- constraints as invariants. This was initially considered part of the Rbc abstraction relation.
-- Actually, the Rbc relation is just an abstraction for ethers.

-- Note that, applied to the Concrete world only, this fails, because the Concrete world
-- is an underconstrained implementation.

assert Ignore_inv {
    all b, b' : ConWorld, m_out : MESSAGE | {
        Between [b]
        Ignore [b, b', m_out]
    } implies Between [b']
}

check Ignore_inv for 5 but 2 ConState -- 5:43 w/o canon, 4:13 w/ canon (siege_v4) -- 5 -- 5:42:14 --4 -- 13:10 (minisat) minisat 10 aborted by user after a 7:08:26 computation
check Ignore_inv for 8 but 2 ConState -- 1:40:22 w/ canon (siege_v4)

assert Increase_inv {
    all b, b' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE | {
        Between [b]
        IncreaseOkay [b, b', p, m_in, m_out]
    } implies Between [b']
}

check Increase_inv for 5 but 2 ConState -- 4 -- 40:24
check Increase_inv for 8 but 2 ConState -- 20:35:33 w/ canon (siege_v4)

assert Abort_inv {
    all b, b' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE | {
        Between [b]
        AbortOkay [b, b', p, m_in, m_out]
    }
    implies Between [b']
}

check Abort_inv for 10 -- 6 -- 20:08:46 -- 4 -- 38:01 (minisat)
check Abort_inv for 5 but 2 ConState -- 5 -- 4:22:24 -- 4 -- 10:40 (minisat)
check Abort_inv for 8 but 2 ConState -- 19:10:12 w/ canon (siege_v4)

pred StartFrom_inv_precond (b, b' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    Between [b]
    StartFromEafrom [b, b', p, m_in, m_out]
}
run StartFrom_inv_precond for 4 but 2 ConState

assert StartFrom_inv {
    all b, b' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE | {
        Between [b]
        StartFromEafrom [b, b', p, m_in, m_out]
    }
    implies Between [b']
}

check StartFrom_inv for 5 but 2 ConState -- 4 -- 38s (minisat)
check StartFrom_inv for 8 but 2 ConState -- 13:16:13 w/ canon (siege_v4)

pred StartTo_inv_precond (b, b' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    Between [b]
    StartToEafrom [b, b', p, m_in, m_out]
}
run StartTo_inv_precond for 4 but 2 ConState


assert StartTo_inv {
    all b, b' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE | {
        Between [b]
        StartToEafrom [b, b', p, m_in, m_out]
    }
    implies Between [b']
}

check StartTo_inv for 5 but 2 ConState -- 4 -- 7s (minisat)
check StartTo_inv for 8 but 2 ConState -- 5:10:13 w/ canon (siege_v4)

pred Req_inv_precond (b, b' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    Between [b]
    ReqOkay [b, b', p, m_in, m_out]
    some m_in.(req <: details).value
}
run Req_inv_precond for 4 but 2 ConState

assert Req_inv {
    all b, b' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE | {
        Between [b]
        ReqOkay [b, b', p, m_in, m_out]
    } implies Between [b']
}

check Req_inv for 5 but 2 ConState -- 4 -- 14s (minisat)
check Req_inv for 8 but 2 ConState -- 20:26:45 w/ canon (siege_v4)

pred Val_inv_precond (b, b' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    Between [b]
    ValOkay [b, b', p, m_in, m_out]
}
run Val_inv_precond for 5 but 2 ConState -- 4 : no instance (SEQNO ?)

assert Val_inv {
    all b, b' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE | {
        Between [b]
        ValOkay [b, b', p, m_in, m_out]
    } implies Between [b']
}

check Val_inv for 5 but 2 ConState -- 4 -- 5s (minisat)
check Val_inv for 8 but 2 ConState -- 8:38:24 w/ canon (siege_v4)

pred Ack_inv_precond (b, b' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    Between [b]
    AckOkay [b, b', p, m_in, m_out]
}
run Ack_inv_precond for 4 but 2 ConState

assert Ack_inv {
    all b, b' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE | {
        Between [b]
        AckOkay [b, b', p, m_in, m_out]
    } implies Between [b']
}

check Ack_inv for 5 but 2 ConState -- 4 -- 15s (minisat)
check Ack_inv for 8 but 2 ConState -- 14:42:13 w/ canon (siege_v4)

pred REL_inv_precond (b, b' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    Between [b]
    ReadExceptionLogEafrom [b, b', p, m_in, m_out]
}
run REL_inv_precond for 4 but 2 ConState

assert ReadExceptionLog_inv {
    all b, b' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE | {
        Between [b]
        ReadExceptionLogEafrom [b, b', p, m_in, m_out]
    } implies Between [b']
}

check ReadExceptionLog_inv for 5 but 2 ConState -- 4 -- 5:07 (minisat)
check ReadExceptionLog_inv for 8 but 2 ConState -- 28:13:00 w/ canon (siege_v4)

pred CEL_inv_precond (b, b' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    Between [b]
    ClearExceptionLogEafrom [b, b', p, m_in, m_out]
}
run CEL_inv_precond for 4 but 2 ConState

assert ClearExceptionLog_inv {
    all b, b' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE | {
        Between [b]
        ClearExceptionLogEafrom [b, b', p, m_in, m_out]
    } implies Between [b']
}

check ClearExceptionLog_inv for 5 but 2 ConState -- 4 -- 18s (minisat)
check ClearExceptionLog_inv for 8 but 2 ConState -- 6:49:54 w/ canon (siege_v4)

assert AuthorizeExLogClear_inv {
    all b, b' : ConWorld, p : ConPurse, m_out : MESSAGE | {
        Between [b]
        AuthorizeExLogClearOkay [b, b', p, m_out]
    } implies Between [b']
}

check AuthorizeExLogClear_inv for 5 but 2 ConState -- 4 -- 1:23 (minisat)
check AuthorizeExLogClear_inv for 8 but 2 ConState -- 26:36:53 w/ canon (siege_v4)

assert Archive_inv {
    all b, b' : ConWorld, m_out : MESSAGE| {
        Between [b]
        Archive [b, b', m_out]
    } implies Between [b']
}

check Archive_inv for 5 but 2 ConState -- 4 -- 4:32 (minisat)
check Archive_inv for 8 but 2 ConState -- 57:49 w/ canon (siege_v4)

-- Decomposition of the operations that first abort.

assert StartFrom_decomp {
    all b, b1, b' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE | {
        Between [b]
        StartFrom [b, b', p, m_in, m_out]
        not Abort [b, b', p, m_in, m_out]
        b1.conAuthPurse = b'.conAuthPurse
        XiConPurse [b1, b', b1.conAuthPurse - p]
        XiConPurseStart [b1, b', p]
        p.status.b1 = eaFrom
        p.nextSeqNo.b1 = p.pdAuth.b'.fromSeqNo
        b1.ether = b.ether
        b1.archive = b.archive
    } implies {
        Abort [b, b1, p, m_in, bottom]
        StartFromEafrom [b1, b', p, m_in, m_out]
    }
}

check StartFrom_decomp for 10 -- 2:36 (minisat)

-- Sanity-check :

pred StartFrom_decomp_ex (b, b1, b' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE) {
    Between [b]
    StartFrom [b, b', p, m_in, m_out]
    not Abort [b, b', p, m_in, m_out]
    p.status.b = epv
    b1.conAuthPurse = b'.conAuthPurse
    XiConPurse [b1, b', b1.conAuthPurse - p]
    XiConPurseStart [b1, b', p]
    p.status.b1 = eaFrom
    p.nextSeqNo.b1 = p.pdAuth.b'.fromSeqNo
    b1.ether = b.ether
    b1.archive = b.archive
}

run StartFrom_decomp_ex for 7

assert StartTo_decomp {
    all b, b1, b' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE | {
        Between [b]
        StartTo [b, b', p, m_in, m_out]
        not Abort [b, b', p, m_in, m_out]
        b1.conAuthPurse = b'.conAuthPurse
        XiConPurse [b1, b', b1.conAuthPurse - p]
        XiConPurseStart [b1, b', p]
        p.status.b1 = eaFrom
        p.nextSeqNo.b1 = p.pdAuth.b'.toSeqNo
        b1.ether = b.ether
        b1.archive = b.archive
    } implies {
        Abort [b, b1, p, m_in, bottom]
        StartToEafrom [b1, b', p, m_in, m_out]
    }
}

check StartTo_decomp for 10 -- 1:15

assert ReadExceptionLog_decomp {
    all b, b1, b' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE | {
        Between [b]
        ReadExceptionLog [b, b', p, m_in, m_out]
        not Abort [b, b', p, m_in, m_out]
        b1.conAuthPurse = b'.conAuthPurse
        XiConPurse [b1, b', b1.conAuthPurse]
        b1.ether = b.ether
        b1.archive = b.archive
    } implies {
        Abort [b, b1, p, m_in, bottom]
        ReadExceptionLogEafrom [b1, b', p, m_in, m_out]
    }
}

check ReadExceptionLog_decomp for 10 -- 1:51 (minisat)

assert ClearExceptionLog_decomp {
    all b, b1, b' : ConWorld, p : ConPurse, m_in, m_out : MESSAGE | {
        Between [b]
        ClearExceptionLog [b, b', p, m_in, m_out]
        not Abort [b, b', p, m_in, m_out]
        b1.conAuthPurse = b'.conAuthPurse
        XiConPurse [b1, b', b1.conAuthPurse - p]
        XiConPurseClear [b1, b', p]
        p.exLog.b1 = m_in.pds
        b1.ether = b.ether
        b1.archive = b.archive
    } implies {
        Abort [b, b1, p, m_in, bottom]
        ClearExceptionLogEafrom [b1, b', p, m_in, m_out]
    }
}

check ClearExceptionLog_decomp for 10 --- 1:28 (minisat)
