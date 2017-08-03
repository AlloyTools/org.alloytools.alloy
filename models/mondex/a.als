module mondex/a
open mondex/common as mondexCOMMON

-- 2006-07-07 DONE

-- State definitions

sig AbWorld {
    abAuthPurse : set AbPurse
}

sig AbPurse in Purse {
    abBalance, abLost : Coin -> AbWorld
}

pred Abstract (s : AbWorld) {
    no s.abAuthPurse.abBalance.s & s.abAuthPurse.abLost.s
    (s.abAuthPurse <: (abBalance + abLost).s) in AbPurse lone -> Coin
--  all c : Coin | lone (abBalance + abLost).s.c & s.abAuthPurse
}

pred XiAbPurse (s, s' : AbWorld, a : set AbPurse) {
    a <: abBalance.s = a <: abBalance.s'
    a <: abLost.s = a <: abLost.s'
}

-- Security properties

fun totalBalance (s : AbWorld) : set Coin {
    s.abAuthPurse.abBalance.s
}

fun totalLost (s : AbWorld) : set Coin {
    s.abAuthPurse.abLost.s
}

pred NoValueCreation (s, s' : AbWorld) {
    totalBalance [s'] in totalBalance [s]
}

pred AllValueAccounted (s, s' : AbWorld) {
    totalBalance [s'] + totalLost [s'] = totalBalance [s] + totalLost [s]
}

-- Messages have to be included.

one sig aNullIn {}
sig AIN in aNullIn + TransferDetails {}

-- there are the ONLY constraints I have over the WHOLE specification.
-- I cannot get rid of those D... facts
fact ain_constr {
    AIN = aNullIn + TransferDetails
}

pred XiAbIn (a, g : AIN) {
    (a + g) in aNullIn or (a + g) in TransferDetails
    (a + g) in TransferDetails implies XiTransfer [a, g]
}

abstract sig AOUT {}
one sig aNullOut extends AOUT {}

-- Operations

pred Authentic (s : AbWorld, p : AbPurse) {
    p in s.abAuthPurse
}

pred SufficientFundsProperty (s : AbWorld, t  :TransferDetails) {
    t.value in t.from.abBalance.s
}

pred AbOp (a_out  : AOUT) {
    a_out = aNullOut
}

pred AbIgnore (s, s' : AbWorld, a_out : AOUT) {
    AbOp [a_out]
    s.abAuthPurse = s'.abAuthPurse
    XiAbPurse [s, s', s.abAuthPurse]
}

pred AbWorldSecureOp (s, s' : AbWorld, a_in : AIN, a_out : AOUT) {
    AbOp [a_out]
    a_in in TransferDetails
    s.abAuthPurse - a_in.from - a_in.to = s'.abAuthPurse - a_in.from - a_in.to
    XiAbPurse [s, s', s.abAuthPurse - a_in.from - a_in.to]
}

pred AbTransferOkay (s, s' : AbWorld, a_in : AIN, a_out : AOUT) {
    AbWorldSecureOp [s, s', a_in, a_out]
    Authentic [s, a_in.from]
    Authentic [s, a_in.to]
    SufficientFundsProperty [s, a_in]
    no a_in.from & a_in.to
    a_in.from.abBalance.s' = a_in.from.abBalance.s - a_in.value
    a_in.from.abLost.s' = a_in.from.abLost.s
    a_in.to.abBalance.s' = a_in.to.abBalance.s + a_in.value
    a_in.to.abLost.s' = a_in.to.abLost.s

    -- ADDED :
    Authentic [s', a_in.from]
    Authentic [s', a_in.to]
}

pred AbTransferLost (s, s' : AbWorld, a_in : AIN, a_out : AOUT) {
    AbWorldSecureOp [s, s', a_in, a_out]
    Authentic [s, a_in.from]
    Authentic [s, a_in.to]
    SufficientFundsProperty [s, a_in]
    no a_in.from & a_in.to
    a_in.from.abBalance.s'  = a_in.from.abBalance.s - a_in.value
    a_in.from.abLost.s' = a_in.from.abLost.s + a_in.value
    XiAbPurse [s, s', a_in.to]

    -- ADDED :
    Authentic [s', a_in.from]
    Authentic [s', a_in.to]
}

pred AbTransfer (s, s' : AbWorld, a_in : AIN, a_out : AOUT) {
    AbTransferOkay [s, s', a_in, a_out] or AbTransferLost [s, s', a_in, a_out] or AbIgnore [s, s', a_out]
}

pred AbInitState (s : AbWorld) {
    Abstract [s]
}

pred AbInitIn (a, g : AIN) {
    XiAbIn [a, g]
}

pred AbFinState (a, g : AbWorld) {
    g.abAuthPurse = a.abAuthPurse
    XiAbPurse [g, a, g.abAuthPurse]
}

pred AbFinOut (a, g : AOUT) {
    a = g
}


-- security properties hold

assert A241 {
    all s, s' : AbWorld, a_in : AIN, a_out : AOUT | {
        Abstract [s]
        Abstract [s']
        AbTransfer [s, s', a_in, a_out]
    } implies {
        NoValueCreation [s, s']
        AllValueAccounted [s, s']
    }
}

check A241 for 10 -- 1:47
--with AbTransferOkay only : 21s -- 9 -- 17s -- 8 -- 9s

pred A240 () {
    some s, s' : AbWorld, a_in : AIN, a_out : AOUT | {
        Abstract [s]
        Abstract [s']
        AbTransferOkay [s, s', a_in, a_out]
        some a_in.value
    }
}

run A240 for 10

-- model consistency

-- some initial state
-- ok, add some constraints
pred AbInitState_ex () {
    some a : AbWorld {
        AbInitState [a]
        some a.abAuthPurse.abBalance.a
        some a.abAuthPurse.abLost.a
    }
}

run AbInitState_ex for 5

-- operations are total
assert AbOp_total {
    all a : AbWorld, a_in : AIN | Abstract [a] implies {
        AbIgnore [a, a, aNullOut]
        AbTransfer [a, a, a_in, aNullOut]
    }
}

check AbOp_total for 10 -- 0:24 (minisat)

-- operations make Abstract constraint hold

assert AbIgnore_inv {
    all a, a' : AbWorld, a_out : AOUT | {
        Abstract [a]
        AbIgnore [a, a', a_out]
    } implies Abstract [a']
}

assert AbTransfer_inv {
    all a, a' : AbWorld, a_in : AIN, a_out : AOUT | {
        Abstract [a]
        AbTransfer [a, a', a_in, a_out]
    } implies Abstract [a']
}

check AbIgnore_inv for 10 -- 0:50 (minisat)
check AbTransfer_inv for 10 -- 8:21 (minisat)
