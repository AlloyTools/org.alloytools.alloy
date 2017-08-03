module mondex/cw
open mondex/c as mondexC
open mondex/common as mondexCOMMON

pred Logbook (log : ConPurse -> PayDetails) {
    all c : ConPurse, pd : PayDetails | (c->pd) in log implies c in pd.(from + to)
}

sig ConWorld extends ConState {
    conAuthPurse : set ConPurse,
    ether : set MESSAGE,
    archive : ConPurse -> PayDetails
}

fun allPayDetails (s : ConWorld) : set PayDetails {
    s.conAuthPurse.(s.archive + (exLog + status.s.(STATUS - eaFrom) <: pdAuth).s) + s.ether.((req <: details) + (val <: details) + (ack <: details) + (exceptionLogResult <: details) + (exceptionLogClear <: pds))
}

pred Concrete_conAuthPurse (s : ConWorld) {
    -- purse spec constraints
    all c : ConPurse | c in s.conAuthPurse implies {
        all p : PayDetails | p in c.exLog.s implies c in p.(from+to)
        c.status.s = epr implies {
            c.pdAuth.s.from = c
            c.pdAuth.s.value in c.balance.s
            Lt [c.pdAuth.s.fromSeqNo, c.nextSeqNo.s]
        }
        c.status.s = epv implies {
            Lt [c.pdAuth.s.toSeqNo, c.nextSeqNo.s]
        }
        c.status.s = epa implies {
            Lt [c.pdAuth.s.fromSeqNo, c.nextSeqNo.s]
        }
    }
}

pred Concrete_archive (s : ConWorld) {
    -- world constraints
    Logbook [s.archive]
    s.archive.PayDetails in s.conAuthPurse
}

-- Concrete_mult and Concrete_PayDetails are actual constraints holding also for the Concrete.
-- They are already defined in the original Z spec, but are modified in some way due to language issues
-- On the contrary, Between_Coin (cf. b module) is due to the representation of the amounts by coins
-- which is a spec issue rather than a language issue

-- To allow the "construction" of a ConWorld by definition of its fields, those have to be declared
-- without any constraints, even multiplicity. To actually "prove the existence" of such objects, one
-- has to show that the ConWorld constraints hold. But those constraints are not only the formulae
-- defined by the Z spec, but also the schema structure, i.e. the "availability" of the fields.

pred Concrete_mult (s : ConWorld) {
    -- multiplicity constraints for well-definedness
    s.conAuthPurse <: status.s in s.conAuthPurse -> one STATUS
    s.conAuthPurse <: nextSeqNo.s in s.conAuthPurse -> one SEQNO
    (s.conAuthPurse :> status.s.(STATUS - eaFrom)) <: pdAuth.s in (s.conAuthPurse :> status.s.(STATUS - eaFrom)) -> one PayDetails
}

-- The PayDetails constraints are only relevant to the ConWorlds. I.e, we do not care about payDetails
-- not occuring in a ConWorld. Hence predicates instead of facts.

-- Since "the combination of purse name and sequence number uniquely identifies the transaction"
-- (PRG-126, p. 24), we may canonicalize all the PayDetails used in the ConWorld.

-- This canonicalization attempt fails because StartFrom or StartTo operations *create* PayDetails,
-- which might exist before (for instance as the counterparty purse's pdAuth).
-- Unless we explicitly enforce it in the StartFromEafrom
-- and the StartToEafrom operations at the world level.

pred PayDetails_canon (s : ConWorld) {
    let f = allPayDetails [s] |
    f->f & from.~from & to.~to & fromSeqNo.~fromSeqNo & toSeqNo.~toSeqNo in iden
}

pred Concrete_PayDetails (s : ConWorld) {
    -- Spec constraint
    let f = allPayDetails [s] | no iden & ~from.(f <: to)

    -- canonicalization
    PayDetails_canon [s]
}

pred Concrete (s : ConWorld) {
    Concrete_conAuthPurse [s]
    Concrete_archive [s]
    Concrete_mult [s]
    Concrete_PayDetails [s]
}

pred ConWorld_ex () {
    some c :ConWorld {
        Concrete [c]
        some c.conAuthPurse
    }
}

run ConWorld_ex for 3
