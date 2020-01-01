sig Time in Int {}
fact positive {all t: Time | t >= 0}
fact noGaps {all t: Time - 0 | minus[t,1] in Time }
one sig BankAccount
{
    deposit: Int one -> Time,
    withdrawal: Int one-> Time,
    balance: Int one-> Time
}
{some deposit and some withdrawal and some balance}
fun depositValue[t: Time]: Int {BankAccount.deposit.t}
fun withdrawalValue[t: Time]: Int {BankAccount.withdrawal.t}
fun balanceValue[t: Time]: Int {BankAccount.balance.t}
pred deposit[t, t' : Time, amount: Int]
{
    amount > 0
    depositValue[t'] = amount
    withdrawalValue[t'] = 0
    balanceValue[t'] = plus[balanceValue[t], amount]
}
pred withdraw[t, t' : Time, amount: Int]
{
    amount > 0
    balanceValue[t] >= amount -- there is enough balance at t
    depositValue[t'] = 0
    withdrawalValue[t'] = amount
    balanceValue[t'] = minus[balanceValue[t], amount]
}

assert sanity
{
    all  t': Time - 0, a : univInt |
    let t = minus[t',1] | -- t' = t + 1
    {
        withdraw[t, t', a]  
        implies
        balanceValue[t'] < balanceValue[t]
    }
}
check sanity

//pred init [t: Time]
//{
//  BankAccount.deposit.t = 0
//  BankAccount.withdrawal.t = 0
//  BankAccount.balance.t = 0
//}

//pred someTransaction[t, t': Time]
//{
//  some amount : Int | deposit[t, t', amount] or withdraw[t, t', amount]
//}
//
//
//pred system
//{
//  init[0]
//  all t: Time - 0 | someTransaction[minus[t, 1] , t]
//}
//
//run scenario
//{
//  init[0]
//  deposit[0, 1, 10]
//  deposit[1, 2, 40]
//  withdraw[2, 3, 30]
//} for 7 Int
//
//pred nonNegative [t: Time]
//{
//  depositValue[t] >= 0 and
//  withdrawalValue[t] >= 0 and
//  balanceValue[t] >= 0
//}
//
