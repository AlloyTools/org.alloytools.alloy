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
(declare-fun |integer/univInt | () (Set (Tuple UInt)))
(declare-fun |this/Time | () (Set (Tuple UInt)))
(declare-fun |this/BankAccount | () (Set (Tuple Atom)))
(declare-fun |this/BankAccount/deposit | () (Set (Tuple Atom UInt UInt)))
(declare-fun |this/BankAccount/withdrawal | () (Set (Tuple Atom UInt UInt)))
(declare-fun |this/BankAccount/balance | () (Set (Tuple Atom UInt UInt)))

; Universe definition for UninterpretedInt
(assert
 (= univInt
   (as univset (Set (Tuple UInt)))))

(assert
 (= |integer/univInt |
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

(define-fun depositValue ((t UInt))  (Set (Tuple UInt))
    (join
       (join |this/BankAccount |  |this/BankAccount/deposit |)
       (singleton (mkTuple t))
    ))

(define-fun withdrawalValue ((t UInt))  (Set (Tuple UInt))
    (join
       (join |this/BankAccount |  |this/BankAccount/withdrawal |)
       (singleton (mkTuple t))
    ))

(define-fun balanceValue ((t UInt))  (Set (Tuple UInt))
    (join
       (join |this/BankAccount |  |this/BankAccount/balance |)
       (singleton (mkTuple t))
    ))


(define-fun deposit ((t1 UInt) (t2 UInt) (amount UInt))  Bool
    (and
        (> (intValue amount) 0) ;  amount > 0
        (= (depositValue t2) (singleton (mkTuple amount))) ;  depositValue[t2] = {amount}
        (= (withdrawalValue t2) (singleton (mkTuple zeroUInt))) ; withdrawalValue[t2] = {0}
        (exists ((x UInt) (y UInt))
           (and
                ; balanceValue[t2] = plus[balanceValue[t1], amount]
                ; x = y + amount
                (=
                    (intValue x)
                    (+ (intValue y) (intValue amount))
                )
                ; balanceValue[t2] = {x}
                (=
                   (singleton (mkTuple x))
                   (join
                       (join
                           |this/BankAccount |
                           |this/BankAccount/balance |
                       )
                       (singleton (mkTuple t2))
                    )
                )
                ; balanceValue[t1] = {y}
                (=
                   (singleton (mkTuple y))
                   (join
                       (join
                           |this/BankAccount |
                           |this/BankAccount/balance |
                       )
                       (singleton (mkTuple t1))
                    )
                )
            )
        )
    )
)



(define-fun withdraw ((t1 UInt) (t2  UInt) (amount UInt))  Bool
    (and
        (> (intValue amount) 0) ;  amount > 0
        ;  balanceValue[t1] >= amount
        (exists ((x UInt))
            (and
                (=
                     (singleton (mkTuple x))
                     (balanceValue t1)
                )
                (>= (intValue x) (intValue amount)
                )
            )
        )
        (= (depositValue t2) (singleton (mkTuple zeroUInt))) ;  depositValue[t2] = {0}
        (= (withdrawalValue t2) (singleton (mkTuple amount))) ; withdrawalValue[t2] = {amount}
        (exists ((x UInt) (y UInt))
           (and
                ; balanceValue[t2] = minus[balanceValue[t1], amount]
                ; x = y - amount
                (=
                    (intValue x)
                    (- (intValue y) (intValue amount))
                )
                ; balanceValue[t2] = {x}
                (=
                   (singleton (mkTuple x))
                   (join
                       (join
                           |this/BankAccount |
                           |this/BankAccount/balance |
                       )
                       (singleton (mkTuple t2))
                    )
                )
                ; balanceValue[t1] = {y}
                (=
                   (singleton (mkTuple y))
                   (join
                       (join
                           |this/BankAccount |
                           |this/BankAccount/balance |
                       )
                       (singleton (mkTuple t1))
                    )
                )
            )
        )
    )
)


; someTransaction
(define-fun someTransaction ((t1 UInt) (t2  UInt))  Bool
    (exists ((amount UInt))
        (or
           (deposit t1 t2 amount)
           (withdraw t1 t2 amount)
        )
    )
)

; system
; init[0]:
(assert
    (and
        ; depositValue[0] = {0}
        (=
            (singleton (mkTuple zeroUInt))
            (depositValue zeroUInt)
        )

        ; withdrawalValue[0] = {0}
        (=
            (singleton (mkTuple zeroUInt))
            (withdrawalValue zeroUInt)
        )

        ; balanceValue[0] = {0}
        (=
            (singleton (mkTuple zeroUInt))
            (balanceValue zeroUInt)
        )
    )
)


; system
; all t': Time - 0 |  let t = minus[t',1]  | someTransaction[t, t']
(assert (forall ((t2 UInt))
    (let
      (( |t' | (mkTuple t2)))
      (=>
        ; t': Time - 0
        (member
            |t' |
            (setminus |this/Time | (singleton (mkTuple zeroUInt))))
        (exists ((t1 UInt))
          (let
            (( |t | (mkTuple t1)))
            (and
              (= (intValue t1) (- (intValue t2) 1)) ; t = t' - 1
              (someTransaction t1 t2)
            )
          )
        )
      )
    )
  )
)

; balanceValue[3] = 50
(assert (exists ((x UInt) (three UInt))
    (and
        (= (intValue x) 50)
        (= (intValue three) 3)
        (=
          (singleton (mkTuple x))
          (balanceValue three)
        )
    )
))


(check-sat)
(get-model)































