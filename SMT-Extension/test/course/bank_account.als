-- inital time step is zero, and each time t is greator than or equal to zero
-- fact {0 in Time and all t: Time | 0 <= t}

sig Time in Int {}

one sig BankAccount 
{
	deposit: Int one -> Time,
	withdrawal: Int one->  Time,
	balance: Int one-> Time, -- accumulated balance
}

fun depositValue[t: Time]: Int {BankAccount.deposit.t}
fun withdrawalValue[t: Time]: Int {BankAccount.withdrawal.t}
fun balanceValue[t: Time]: Int {BankAccount.balance.t}

pred deposit[t, t' : Time, amount: Int]
{
	{
		depositValue[t'] = amount
	  	withdrawalValue[t'] = 0
		balanceValue[t'] = plus[balanceValue[t], amount]
	}
}

pred withdraw[t, t' : Time, amount: Int]
{	
	amount > 0
	{
		balanceValue[t] >= amount -- there is enough balance
		depositValue[t'] = 0
	  	withdrawalValue[t'] = amount
		balanceValue[t'] = minus[balanceValue[t'], amount]
	}
}

pred init [t: Time]
{  
 	BankAccount.deposit.0 = 0
	BankAccount.withdrawal.0 = 0
	BankAccount.balance.0 = 0
}

pred someTransaction[t, t': Time] 
{
	some amount : Int | deposit[t, t', amount] or withdraw[t, t', amount]	
}

fact system {
  init[0]
  all t: Time - 0, account: BankAccount |
    someTransaction[t, plut[t, 1]]
}

run {
--deposit[1, 2, 10] 
--deposit[checkAccount, 2, 4] 
--withdraw[checkAccount, 3, 2]
} for 5 Int

assert nonNegative { 
	all t: Time, account: BankAccount |
	depositValue[account, t] >= 0 and
	withdrawalValue[account, t] >= 0 and
	balanceValue[account, t] >= 0
}

check nonNegative
