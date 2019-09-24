sig Time in Int{}
-- inital time step is zero, and each time t is greator than or equal to zero
fact {0 in Time and all t: Time | 0 <= t}

abstract sig BankAccount {
	deposit: Int one -> Time,
	withdrawal: Int one->  Time,
	balance: Int one-> Time, -- accumulated balance
}

one sig checkAccount extends BankAccount {}

pred openAccount[account: BankAccount]
{
	account.deposit.0 = 0
	account.withdrawal.0 = 0
	account.balance.0 = 0
}

fun depositValue[account: BankAccount, t: Time]: Int {account.deposit.t}
fun withdrawalValue[account: BankAccount, t: Time]: Int {account.withdrawal.t}
fun balanceValue[account: BankAccount, t: Time]: Int {account.balance.t}

pred deposit[account: BankAccount, t : Time, amount: Int]
{	
	t > 0 and amount > 0
	let t' = {minus[t, 1]	} |
	{
		depositValue[account, t] = amount
	  	withdrawalValue[account, t] = 0
		balanceValue[account, t] = plus[balanceValue[account, t'], amount]
	}
}

pred withdraw[account: BankAccount, t : Time, amount: Int]
{	
	t > 0 and amount > 0
	let t' = {minus[t, 1]	} |
	{
		balanceValue[account, t'] >= amount -- there is enough balance
		depositValue[account, t] = 0
	  	withdrawalValue[account, t] = amount
		balanceValue[account, t] = minus[balanceValue[account, t'], amount]
	}
}

fact init{openAccount [checkAccount]}

pred someTransaction[account: BankAccount, t: Time] {
       t > 0
	some amount: Int | amount > 0 and 
	(deposit[checkAccount, t, amount] or withdraw[checkAccount, t, amount])	
}

fact system {
  all t: Time - 0, account: BankAccount |
    someTransaction[account, t]
}

run {
deposit[checkAccount, 1, 3] 
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
