sig Time in Int{}

-- inital time step is zero, each time is greator than or equal to zero
fact {0 in Time and all x: Time | 0 <= x}


sig Account {
	debit: Int one -> Time ,
	credit: Int one->  Time,
	balance: Int one-> Time -- accumulated balance
}

one sig checkAccount, savingAccount, investingAccount extends Account {}

pred openAccount[account: Account] 
{
	account.debit.0 = 0
	account.credit.0 = 0
	account.balance.0 = 0
}

fun debitValue[account: Account, t: Time]: Int {account.debit.t}
fun creditValue[account: Account, t: Time]: Int {account.credit.t}
fun balanceValue[account: Account, t: Time]: Int {account.balance.t}

pred deposit[account: Account, t : Time, amount: Int]
{
	let t' = {plus[t, 1]	} | 
	{
		debitValue[account, t'] = amount
	  	creditValue[account, t'] = 0
		balanceValue[account, t'] = plus[balanceValue[account, t], amount]
	}
}

pred transitions[t,t': Time] {
	1 = 1
}

fact init{
  	openAccount [checkAccount]
        deposit[checkAccount, 0, 3] -- deposit 3
        deposit[checkAccount, 1, 5] -- deposit 2 
        deposit[checkAccount, 2, 3] -- deposit 1
        deposit[checkAccount, 3, 5] -- withdrow 5
}

