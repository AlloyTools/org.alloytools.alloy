module tests/test // example by Alan Shaffer

sig State {
    vars: Variable -> one Value,
    label: Variable -> one Label,
    debug_filter_result: Filter
}

enum Variable { x1 }

enum Label { High, Mid, Low }
one sig Policy { ord: Label -> Label }
{   ord = ^( (Low -> Mid)
            + (Mid -> High) )
            + (iden & (Label -> Label) )
}

enum Value { const_minus_2, const_minus_1, const0, const1, const2 }
one sig LT { lt:  Value -> Value }
{  lt = ^(
        (  const_minus_2      ->   const_minus_1)
     +  (  const_minus_1      ->   const0)
     + (  const0      ->   const1)
     + (  const1      ->   const2)
) }

one sig InitialState extends State {}
{
    vars = (Variable -> const1)
    label = (Variable -> High)
    debug_filter_result.val = const_minus_1
    debug_filter_result.lab = Low
}

fun filter [v1: Value, a1: Label]: Filter {
    { result: Filter | {
        result.val = (((v1->const0) in LT.lt) => const0 else v1)
        result.lab = (((a1->Mid) in Policy.ord) => Mid else a1)
        }
    }
}

sig Filter {
    val:    Value,
    lab:    Label
}

fact { all st1: State - InitialState | some st: State | let temp = filter[ const_minus_1, Low ] |
    (
             st1.debug_filter_result = temp &&
             st1.vars = st.vars ++ ( x1 -> temp.val ) &&
             st1.label = st.label ++ ( x1 -> temp.lab )
    )
}

pred show () {}
run show for 5 but exactly 2 State expect 1
