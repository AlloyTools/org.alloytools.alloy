(set-logic ALL)
(set-option :tlimit 60000)
(set-option :produce-unsat-cores false)
(set-option :block-models literals)
(set-option :finite-model-find true)
(set-option :produce-models true)
(set-option :incremental true)
(set-option :sets-ext true)
(declare-sort Atom 0)
(declare-sort UInt 0)
(declare-fun intValue (UInt) Int)
(declare-fun atomNone () (Set (Tuple Atom)))
(declare-fun univAtom () (Set (Tuple Atom)))
(declare-fun idenAtom () (Set (Tuple Atom Atom)))
(declare-fun idenInt () (Set (Tuple UInt UInt)))
(declare-fun univInt () (Set (Tuple UInt)))
(declare-fun |this/Time | () (Set (Tuple UInt)))
(declare-fun |this/BankAccount | () (Set (Tuple Atom)))
(declare-fun |this/BankAccount/deposit | () (Set (Tuple Atom UInt UInt)))
(declare-fun |this/BankAccount/withdrawal | () (Set (Tuple Atom UInt UInt)))
(declare-fun |this/BankAccount/balance | () (Set (Tuple Atom UInt UInt)))

; Universe definition for UninterpretedInt
(assert 
 (= univInt 
   (as univset (Set (Tuple UInt)))))

; fact positive {all t: Time | t >= 0}
(assert (forall ((t UInt)) 
    (=>
        (member (mkTuple t) |this/Time |)
        (>= (intValue t) 0))
    )
)

; fact noGaps {all t: Time - 0 | minus[t,1] in Time }
(assert (forall ((t UInt)) 
    (=>
        (and
            (member (mkTuple t) |this/Time |)
            (> (intValue t) 0) ; t: Time - 0
        )
        (exists ((x UInt)) 
            (and
                ; x = t - 1
                (= (intValue x) (- (intValue t) 1))
                (member (mkTuple x) |this/Time |)
            )
        )
    )
))

; BankAccount multiplicity
(assert (exists ((x Atom)) (= |this/BankAccount | (singleton (mkTuple x)))))

; deposit subset 
(assert 
    (subset
        |this/BankAccount/deposit |
        (product 
            (product |this/BankAccount | univInt)
            |this/Time |
        )
    )
)

; deposit multiplicity 
(assert (forall ((x Atom)) 
    (=>
        (exists ((y UInt) (z UInt))
            (member (mkTuple x y z) |this/BankAccount/deposit |)
        )
        (forall ((z UInt))
            (=>
                (member (mkTuple z) |this/Time |) ; antecedent
                (exists ((y UInt))
                    (and
                        (member (mkTuple x y z) |this/BankAccount/deposit |)
                        (forall ((w UInt))
                            (=> 
                                (member (mkTuple x w z) |this/BankAccount/deposit |)
                                (= y w)
                            )
                        )
                    )
                )
            )   
        )
    )))


; withdrawal subset 
(assert 
    (subset
        |this/BankAccount/withdrawal |
        (product 
            (product |this/BankAccount | univInt)
            |this/Time |
        )
    )
)

; withdrawal multiplicity 
(assert (forall ((x Atom)) 
    (=>
        (exists ((y UInt) (z UInt))
            (member (mkTuple x y z) |this/BankAccount/withdrawal |)
        )
        (forall ((z UInt))
            (=>
                (member (mkTuple z) |this/Time |)
                (exists ((y UInt))
                    (and
                        (member (mkTuple x y z) |this/BankAccount/withdrawal |)
                        (forall ((w UInt))
                            (=> 
                                (member (mkTuple x w z) |this/BankAccount/withdrawal |)
                                (= y w)
                            )
                        )
                    )
                )
            )   
        )
    )))
    
; balance subset 
(assert 
    (subset
        |this/BankAccount/balance |
        (product 
            (product |this/BankAccount | univInt)
            |this/Time |
        )
    )
)

; balance multiplicity 
(assert (forall ((x Atom)) 
    (=>
        (exists ((y UInt) (z UInt))
            (member (mkTuple x y z) |this/BankAccount/balance |)
        )
        (forall ((z UInt))
            (=>
                (member (mkTuple z) |this/Time |)
                (exists ((y UInt))
                    (and
                        (member (mkTuple x y z) |this/BankAccount/balance |)
                        (forall ((w UInt))
                            (=> 
                                (member (mkTuple x w z) |this/BankAccount/balance |)
                                (= y w)
                            )
                        )
                    )
                )
            )   
        )
    )))
    
; signature fact: nonempty deposit
( assert 
    (forall ((x Atom))
        (=>
            (member (mkTuple x) |this/BankAccount |)
            (exists ((y UInt) (z UInt))
                (member
                    (mkTuple x y z)
                    |this/BankAccount/deposit |
                )
            )
        )
    )
)

; signature fact: nonempty withdrawal
( assert 
    (forall ((x Atom))
        (=>
            (member (mkTuple x) |this/BankAccount |)
            (exists ((y UInt) (z UInt))
                (member
                    (mkTuple x y z)
                    |this/BankAccount/withdrawal |
                )
            )
        )
    )
)

; signature fact: nonempty balance
( assert 
    (forall ((x Atom))
        (=>
            (member (mkTuple x) |this/BankAccount |)
            (exists ((y UInt) (z UInt))
                (member
                    (mkTuple x y z)
                    |this/BankAccount/balance |
                )
            )
        )
    )
)



; intValue is injective
(assert 
 (forall ((x UInt)(y UInt)) 
   (=> 
     (not 
       (= x y)) 
     (not 
       (= (intValue x) (intValue y))))))

; int zero
(declare-const zeroUInt UInt)
(assert (= (intValue zeroUInt) 0))


; system
(assert (not 
    (forall ((u UInt) (v UInt))
        (let 
            (( |t' | (mkTuple u)) (|a | (mkTuple v)))
            (=>
                (and
                    (member 
                        |t' | 
                        (setminus |this/Time | (singleton (mkTuple zeroUInt))))
                    (member |a | univInt)
                )
                (exists ((w UInt))
                    (let 
                        (( |t | (mkTuple w)))
                        (and
                            (= (intValue w) (- (intValue u) 1)) ; t = t' - 1
                            (=>
                               (and
                                   ; a > 0
                                   (> (intValue v) 0) 
                                   ;  balanceValue[t] >= a
                                   (exists ((x UInt))
                                       (and
                                            (=
                                                (singleton (mkTuple x))
                                               (join
                                                   (join 
                                                       |this/BankAccount |
                                                       |this/BankAccount/balance |
                                                   )
                                                   (singleton |t |)
                                                )
                                            )
                                            (>= (intValue x) (intValue v))
                                        )
                                    )
                                    ; widthdraw[t, t', a] 
                                   (exists ((x UInt) (y UInt))
                                       (and
                                            ; balanceValue[t'] = {x}
                                            (=
                                                (singleton (mkTuple x))
                                               (join
                                                   (join 
                                                       |this/BankAccount |
                                                       |this/BankAccount/balance |
                                                   )
                                                   (singleton |t' |)
                                                )
                                            )
                                            ; balanceValue[t] = {y}
                                            (=
                                                (singleton (mkTuple y))
                                               (join
                                                   (join 
                                                       |this/BankAccount |
                                                       |this/BankAccount/balance |
                                                   )
                                                   (singleton |t |)
                                                )
                                            )
                                            ; balanceValue[t'] = minus[balanceValue[t], a]
                                            (= 
                                                (intValue x) 
                                                (- (intValue y) (intValue v))
                                            )
                                            ; depositValue[t'] = {zeroUInt}
                                            (=
                                               (singleton (mkTuple zeroUInt))
                                               (join
                                                   (join 
                                                       |this/BankAccount |
                                                       |this/BankAccount/deposit |
                                                   )
                                                   (singleton |t' |)
                                                )
                                            )
                                            ; withdrawalValue[t'] = {a}
                                            (=
                                               (singleton |a |)
                                               (join
                                                   (join 
                                                       |this/BankAccount |
                                                       |this/BankAccount/withdrawal |
                                                   )
                                                   (singleton |t' |)
                                                )
                                            )
                                        )
                                    )
                               )
                               (exists ((x UInt) (y UInt))
                                       (and
                                            ; balanceValue[t'] = {x}
                                            (=
                                                (singleton (mkTuple x))
                                               (join
                                                   (join 
                                                       |this/BankAccount |
                                                       |this/BankAccount/balance |
                                                   )
                                                   (singleton |t' |)
                                                )
                                            )
                                            ; balanceValue[t] = {y}
                                            (=
                                                (singleton (mkTuple y))
                                               (join
                                                   (join 
                                                       |this/BankAccount |
                                                       |this/BankAccount/balance |
                                                   )
                                                   (singleton |t |)
                                                )
                                            )
                                            ; balanceValue[t'] < balanceValue[t]
                                            (< (intValue x) (intValue y))
                                        )
                                )
                            )
                        )
                    )
                )
            )
        )
    )
))

; init[0]: BankAccount.deposit.0 = 0
(assert 
    ; depositValue[0] = {0}
    (=
        (singleton (mkTuple zeroUInt))
       (join
           (join 
               |this/BankAccount |
               |this/BankAccount/deposit |
           )
           (singleton (mkTuple zeroUInt))
        )
    )
)

; init[0]: BankAccount.withdrawal.0 = 0
(assert 
    ; withdrawalValue[0] = {0}
    (=
        (singleton (mkTuple zeroUInt))
       (join
           (join 
               |this/BankAccount |
               |this/BankAccount/withdrawal |
           )
           (singleton (mkTuple zeroUInt))
        )
    )
)

; init[0]: BankAccount.balance.0 = 0
(assert 
    ; withdrawalValue[0] = {0}
    (=
        (singleton (mkTuple zeroUInt))
       (join
           (join 
               |this/BankAccount |
               |this/BankAccount/balance |
           )
           (singleton (mkTuple zeroUInt))
        )
    )
)

(check-sat)
(get-model)































