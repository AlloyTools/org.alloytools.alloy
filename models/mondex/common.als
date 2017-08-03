module mondex/common

sig Coin {}

-- Purse represents the identities of purses. It is not intended to be used by itself.
-- But nor is it intended to be abstract and extended by AbPurse and Conpurse, because
-- those signatures both have to have a nonempty intersection in order to allow Abstract and Concrete
-- purses having the same identity.

sig Purse {}

sig TransferDetails {
    from, to : Purse, value : set Coin
}

pred XiTransfer (p, p' : TransferDetails) {
    p.from = p'.from
    p.to = p'.to
    p.value = p'.value
}
