module tests/test // Bugpost by jeanf.molderez@yahoo.com

open util/ordering[State] as ord
------------- The State signature -----------------------
sig State {
nextState: State, // each State has one successor
linearNext : lone State,
A : Obj -> Obj,
B : Obj -> Obj
}
sig Obj {}
fact TraceConstraints {
all s : State | s.linearNext = next[s]
State in ord/first.*nextState
all s : State - ord/last |
s.nextState = s.linearNext
}
------------- The LTL until operator ---------------------
fun intervalStates[stInitial, stFinal : State]:set State {
stInitial = stFinal
=>
stInitial
else
( stFinal in stInitial.^linearNext )
=>
stInitial.*linearNext & stFinal.^(~linearNext)
else
stInitial.*linearNext +
( stFinal.^(~linearNext) & stInitial.*nextState )
}
pred Until(st: State, X: State -> Obj -> Obj,
Y: State ->Obj -> Obj, o1, o2 : Obj )
{
some st1 : st.*nextState | {
o2 in st1.Y[o1]
( all st' : intervalStates[st, st1] | o2 in st'.X[o1] )
}
}

------------- Simulations -------------------------------
pred show() {}
run show for 5 expect 1

