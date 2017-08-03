module mondex/rab

open mondex/bop as mondexBOP
open mondex/bcif as mondexBCIF
open mondex/b as mondexB
open mondex/cw as mondexCW
open mondex/c as mondexC
open mondex/a as mondexA
open mondex/common as mondexCOMMON

-- Abstract/Between refinement

-- NOTE : The following statement may be commented or not
-- depending on whether global canonicalization is wanted
open mondex/canon as mondexCANON


pred RabCl_constr (a : AbWorld, b : ConWorld, cl : set PayDetails) {
    a.abAuthPurse = b.conAuthPurse
    abLost.a = ((b.conAuthPurse->(definitelyLost[b] + cl)) & ~from).value
    abBalance.a = ((b.conAuthPurse->(maybeLost[b] - cl)) & ~to).value + balance.b
}

pred RabCl_cond (b : ConWorld, cl : set PayDetails) {
    cl in maybeLost [b]
}

pred RabCl (a : AbWorld, b : ConWorld, cl : set PayDetails) {
    RabCl_cond [b, cl]
    RabCl_constr [a, b, cl]
}

-- Let's try to get rid of the cl quantification. The thing is that, given the abLost, I may find the abBalance
-- thanks to the coins, and the fact that "no ~from & ~to" holds.

pred RabCl2 (a : AbWorld, b : ConWorld) {
    a.abAuthPurse = b.conAuthPurse
    let ipd = definitelyLost [b] + maybeLost [b] |
    let min = b.conAuthPurse <: ~from :> definitelyLost [b] |
    let mbLost = b.conAuthPurse->maybeLost[b] {
        min.value in abLost.a
        abLost.a in (min + (mbLost & ~from)).value
-- the following constraint ensures that whenever a coin of one PayDetails is in the amount, so are all of its other coins
        abLost.a.(~value :> ipd).value in abLost.a
        let cl = ~to :> (b.conAuthPurse.abLost.a.(~value :> ipd) - b.conAuthPurse.min) | abBalance.a = balance.b + ((mbLost & ~to) - cl).value
    }
}

-- I have to show that if RabCl holds, then RabCl2 holds, in order to use BOTH RabCl and RabCl2 in the proofs :
-- RabCl2 in the hypotheses, RabCl in the conclusion. But, to use RabCl in the conclusion, I also need a way to extract the chosenLost set
-- from RabCl2. I can do it, thanks to this function :

fun chosenLost (a : AbWorld, b : ConWorld) : set TransferDetails {
    b.conAuthPurse.(abLost.a.(~value :> maybeLost [b]))
}

-- To ensure that this set is actually the right one, I would need to show the other way, i.e. RabCl2 implies RabCl with the chosenLost
-- given by that function above :

assert Rab_cl2_cl {
    all a : AbWorld, b : ConWorld | {
        Between [b]
        RabCl2 [a, b]
    }
    implies RabCl [a, b, chosenLost [a, b]]
}

check Rab_cl2_cl for 10 -- 3161s (siege_v4) -- 4 -- 3:33 (minisat)

-- But for the interesting way, I still need to "quantify" over chosenLost.

sig cl' in PayDetails {}

-- If both assertions hold, then Rab_cl_cl2 will be the ONLY point in the spec where I'll have to 2nd-order-quantify. Elsewhere,
-- in particular in the Rab_op proofs, I'll use RabCl2 instead of quantification.

assert Rab_cl_cl2 {
    all a : AbWorld, b : ConWorld | {
        Between [b]
        RabCl [a, b, cl']
    } implies RabCl2 [a, b]
}

check Rab_cl_cl2 for 10
--when using a ChosenLost sig: 3454s (siege_v4) -- 6 -- 22:30 -- 5 -- 2:55 -- 4 -- 0:26 (minisat)
-- took between 1 and 2 days (no accurate time indication available) when using no sig


assert Rab_ex_2 {
    all a : AbWorld, b : ConWorld | {
        RabCl [a, b, cl']
        Between [b]
    } implies Abstract [a]
}

-- check Rab_ex for 9 -- 10:25:45 -- 8 -- 31:28 -- 7 -- 9:48 -- 6 -- 9:19 -- 5 -- 1:45 (minisat)

pred RabIn (a : AIN, m : MESSAGE) {
    InitIn [a, m]
}

pred RabOut (a : AOUT, m : MESSAGE) {
    FinOut [a]
}

assert Rab_init_2 {
    all a : AbWorld, b : ConWorld | {
        RabCl [a, b, cl']
        BetwInitState [b]
    } implies {
        AbInitState [a]
    }
}

check Rab_init_2 for 5 -- 2:02 (berkmin)

pred Rab_init_precond (a : AbWorld, b : ConWorld) {
    RabCl2 [a, b]
    BetwInitState [b]
}
run Rab_init_precond for 5 but 1 AbWorld, 1 ConState

assert Rab_init {
    all a : AbWorld, b : ConWorld | Rab_init_precond [a, b] implies AbInitState [a]
}

check Rab_init for 6 but 1 AbWorld, 1 ConState -- 5:1,1 : 34s

pred Rab_fin_precond (a, g : AbWorld, b : ConWorld) {
    FinState [b, g]
    RabCl [a, b, maybeLost [b]]
    Between [b]
    Abstract [g]
}
run Rab_fin_precond for 5 but 2 AbWorld, 1 ConState

assert Rab_fin {
    all a,g : AbWorld, b : ConWorld | Rab_fin_precond [a, g, b] implies {
        AbFinState [a, g]
    }
}

check Rab_fin for 6 but 2 AbWorld, 1 ConState -- 5 -- 13s (minisat)


assert Rab_ignore_2 {
    all a, a' : AbWorld, b, b' : ConWorld, a_out : AOUT, m_out : MESSAGE  | {
        RabCl [a, b, cl']
        RabCl [a', b', cl']
        RabOut [a_out, m_out]
        Ignore [b, b', m_out]
        Between [b]
        Between [b']
    } implies AbIgnore [a, a', a_out]
}

check Rab_ignore_2 for 8 -- 1:47:03 -- 7 -- 27:40 -- 6 -- 5:15 -- 5 -- 00:46 -- 4 -- 00:27 (minisat)


-- In fact there is an error in the proofs of the former specification (like RabCl_ignore_2 above) :
-- RabCl as an hypothesis is thought to be a constructive predicate (defining a by equalities from b),
-- but it also contains a hidden constraint over ChosenLost. Now I see that I have to split those two aspects,
-- and say : RabCl_constr is the constructive predicate, and RabCl is RabCl_constr conjoined with the constraint

-- Other proofs now led with RabCl2' -> RabCl

assert Rab_ignore {
    all a, a' : AbWorld, b, b' : ConWorld, a_out :AOUT, m_out:MESSAGE | {
        RabCl2 [a', b']
        RabCl_constr [a, b, chosenLost [a', b']]
        RabOut [a_out, m_out]
        Ignore [b, b', m_out]
        Between [b]
        Between [b']
    } implies {
        RabCl [a, b, chosenLost [a', b']]
        AbIgnore [a, a', a_out]
    }
}

check Rab_ignore for 6 -- 24:39
check Rab_ignore for 8 but 2 AbWorld, 2 ConState -- 38:14 w/canon -- 6 -- 7:20 w/ canon, 17:09 w/o canon (siege_v4)

assert Rab_increase {
    all a, a' : AbWorld, b, b' : ConWorld, p : ConPurse, a_in : AIN, a_out :AOUT, m_in, m_out:MESSAGE | {
        RabCl2 [a', b']
        RabCl_constr [a, b, chosenLost [a', b']]
        RabIn [a_in, m_in]
        RabOut [a_out, m_out]
        IncreaseOkay [b, b', p, m_in, m_out]
        Between [b]
        Between [b']
    } implies {
        RabCl_cond [b, chosenLost [a', b']]
        AbIgnore [a, a', a_out]
    }
}

check Rab_increase for 8 but 2 AbWorld, 2 ConState -- 58:23 w/canon -- 6 -- 14:01 w/canon, 42:12 w/o canon (siege_v4) -- 5 -- 1:23:49 (minisat)

assert Rab_abort {
    all a, a2, a' : AbWorld, b, b' : ConWorld, p : ConPurse, a_in : AIN, a_out :AOUT, m_in, m_out:MESSAGE | {
        RabCl2 [a', b']
        RabCl_constr [a, b, chosenLost [a', b']]
        RabCl_constr [a2, b, chosenLost [a', b'] + p.pdAuth.b]
        RabIn [a_in, m_in]
        RabOut [a_out, m_out]
        AbortOkay [b, b', p, m_in, m_out]
        Between [b]
        Between [b']
    } implies {
        {
            RabCl_cond [b, chosenLost [a', b']]
            AbIgnore [a, a', a_out]
        } or {
            RabCl_cond [b, chosenLost [a', b'] + p.pdAuth.b]
            AbIgnore [a2, a', a_out]
        }
    }
}

check Rab_abort for 10 -- 61443s (siege_v4)
check Rab_abort for 8 but 2 AbWorld, 2 ConState -- 1:20:34 w/ canon -- 6 -- 36:07 w/o canon, 16:00 w/ canon

assert Rab_startFrom {
    all a, a' : AbWorld, b, b' : ConWorld, p : ConPurse, a_in : AIN, a_out : AOUT, m_in, m_out : MESSAGE | {
        RabCl2 [a', b']
        RabCl_constr [a, b, chosenLost [a', b']]
        RabIn [a_in, m_in]
        RabOut [a_out, m_out]
        StartFromEafrom [b, b', p, m_in, m_out]
        Between [b]
        Between [b']
    } implies {
        RabCl_cond [b, chosenLost [a', b']]
        AbIgnore [a, a', a_out]
    }
}

check Rab_startFrom for 8 but 2 AbWorld, 2 ConState -- 48:05 w/ canon (siege_v4) -- 5 -- 41:37 (minisat)

pred Rab_startTo_precond (a, a' : AbWorld, b, b' : ConWorld, p : ConPurse, a_in : AIN, a_out : AOUT, m_in, m_out : MESSAGE) {
    RabCl2 [a', b']
    RabCl_constr [a, b, chosenLost [a', b']]
    RabIn [a_in, m_in]
    RabOut [a_out, m_out]
    StartToEafrom [b, b', p, m_in, m_out]
    Between [b]
    Between [b']
    some m_in.value
    m_in.counterParty in b.conAuthPurse
}

run Rab_startTo_precond for 5 but 2 AbWorld, 2 ConState

assert Rab_startTo {
    all a, a' : AbWorld, b, b' : ConWorld, p : ConPurse, a_in : AIN, a_out : AOUT, m_in, m_out : MESSAGE | {
        RabCl2 [a', b']
        RabCl_constr [a, b, chosenLost [a', b']]
        RabIn [a_in, m_in]
        RabOut [a_out, m_out]
        StartToEafrom [b, b', p, m_in, m_out]
        Between [b]
        Between [b']
    } implies {
        RabCl_cond [b, chosenLost [a', b']]
        AbIgnore [a, a', a_out]
    }
}

check Rab_startTo for 8 but 2 AbWorld, 2 ConState -- 1:01:23 w/ canon (siege_v4) -- 5 -- 1:01 (minisat)

assert Rab_req {
    all a, a' : AbWorld, b, b' : ConWorld, p : ConPurse, a_in : AIN, a_out : AOUT, m_in, m_out : MESSAGE | {
        RabCl2 [a', b']
        RabCl_constr [a, b, chosenLost [a', b'] - p.pdAuth.b]
        RabIn [a_in, m_in]
        RabOut [a_out, m_out]
        ReqOkay [b, b', p, m_in, m_out]
        Between [b]
        Between [b']
    } implies {
        RabCl_cond [b, chosenLost [a', b'] - p.pdAuth.b]
        AbTransfer [a, a', a_in, a_out]
    }
}

check Rab_req for 8 but 2 AbWorld, 2 ConState -- 42:26 w/ canon (siege_v4) -- 5 -- 58:28 (minisat)

pred Rab_val_precond (a, a' : AbWorld, b, b' : ConWorld, p : ConPurse, a_in : AIN, a_out : AOUT, m_in, m_out : MESSAGE) {
    RabCl2 [a', b']
    RabCl_constr [a, b, chosenLost [a', b']]
    RabIn [a_in, m_in]
    RabOut [a_out, m_out]
    ValOkay [b, b', p, m_in, m_out]
    Between [b]
    Between [b']
    some m_in.(val <: details).value
    m_in.(val <: details).(from + to) in b.conAuthPurse
}

run Rab_val_precond for 5 but 2 AbWorld, 2 ConState

assert Rab_val {
    all a, a' : AbWorld, b, b' : ConWorld, p : ConPurse, a_in : AIN, a_out : AOUT, m_in, m_out : MESSAGE | {
        RabCl2 [a', b']
        RabCl_constr [a, b, chosenLost [a', b']]
        RabIn [a_in, m_in]
        RabOut [a_out, m_out]
        ValOkay [b, b', p, m_in, m_out]
        Between [b]
        Between [b']
    } implies {
        RabCl_cond [b, chosenLost [a', b']]
        AbIgnore [a, a', a_out]
    }
}

check Rab_val for 8 but 2 AbWorld, 2 ConState -- 25:35 w/canon (siege_v4) -- 5 -- 21s (minisat)

assert Rab_ack {
    all a, a' : AbWorld, b, b' : ConWorld, p : ConPurse, a_in : AIN, a_out : AOUT, m_in, m_out : MESSAGE | {
        RabCl2 [a', b']
        RabCl_constr [a, b, chosenLost [a', b']]
        RabIn [a_in, m_in]
        RabOut [a_out, m_out]
        AckOkay [b, b', p, m_in, m_out]
        Between [b]
        Between [b']
    } implies {
        RabCl_cond [b, chosenLost [a', b']]
        AbIgnore [a, a', a_out]
    }
}

check Rab_ack for 8 but 2 AbWorld, 2 ConState -- 40:44 w/ canon (siege_v4) -- 5 -- 9:35 (minisat)

assert Rab_readExceptionLog {
    all a, a' : AbWorld, b, b' : ConWorld, p : ConPurse, a_in : AIN, a_out : AOUT, m_in, m_out : MESSAGE | {
        RabCl2 [a', b']
        RabCl_constr [a, b, chosenLost [a', b']]
        RabIn [a_in, m_in]
        RabOut [a_out, m_out]
        ReadExceptionLogEafrom [b, b', p, m_in, m_out]
        Between [b]
        Between [b']
    } implies {
        RabCl_cond [b, chosenLost [a', b']]
        AbIgnore [a, a', a_out]
    }
}

check Rab_readExceptionLog for 8 but 2 AbWorld, 2 ConState -- 38:06 w/ canon (siege_v4) -- 5 -- 1:52:31 (minisat)

assert Rab_clearExceptionLog {
    all a, a' : AbWorld, b, b' : ConWorld, p : ConPurse, a_in : AIN, a_out : AOUT, m_in, m_out : MESSAGE | {
        RabCl2 [a', b']
        RabCl_constr [a, b, chosenLost [a', b']]
        RabIn [a_in, m_in]
        RabOut [a_out, m_out]
        ClearExceptionLogEafrom [b, b', p, m_in, m_out]
        Between [b]
        Between [b']
    } implies {
        RabCl_cond [b, chosenLost [a', b']]
        AbIgnore [a, a', a_out]
    }
}

check Rab_clearExceptionLog for 8 but 2 AbWorld, 2 ConState -- 35:01 w/ canon (siege_v4) -- 5 -- 6:00 (minisat)

assert Rab_authorizeExLogClear {
    all a, a' : AbWorld, b, b' : ConWorld, p : ConPurse, a_in : AIN, a_out : AOUT, m_in, m_out : MESSAGE | {
        RabCl2 [a', b']
        RabCl_constr [a, b, chosenLost [a', b']]
        RabIn [a_in, m_in]
        RabOut [a_out, m_out]
        AuthorizeExLogClearOkay [b, b', p, m_out]
        Between [b]
        Between [b']
    } implies {
        RabCl_cond [b, chosenLost [a', b']]
        AbIgnore [a, a', a_out]
    }
}

check Rab_authorizeExLogClear for 8 but 2 AbWorld, 2 ConState -- 18:34 w/ canon (siege_v4) -- 5 -- 53:52 (minisat)

assert Rab_archive {
    all a, a' : AbWorld, b, b' : ConWorld, a_out : AOUT, m_out : MESSAGE | {
        RabCl2 [a', b']
        RabCl_constr [a, b, chosenLost [a', b']]
        RabOut [a_out, m_out]
        Archive [b, b', m_out]
        Between [b]
        Between [b']
    } implies {
        RabCl_cond [b, chosenLost [a', b']]
        AbIgnore [a, a', a_out]
    }
}

check Rab_archive for 5 -- 40:25 (minisat)
check Rab_archive for 8 but 2 AbWorld, 2 ConState -- 29:01 w/ canon (siege_v4)
