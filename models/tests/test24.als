module tests/test // Bugpost by robin.van.remortel@gmail.com

abstract sig Fruit
{
relation: Banana one -> one Orange
}

abstract sig SweetFruit extends Fruit {}

one sig Orange, Banana extends SweetFruit {}

fact
{
all f:Fruit | ~(f.relation) = Orange -> Banana
}

pred show() {}

run show for 5 expect 1
