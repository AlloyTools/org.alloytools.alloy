module dating // Bugpost by J.G.M. Derriks (Jan.Derriks@student.uva.nl)

abstract sig School {}
abstract sig Hobby {}
one sig Elementary, Intermediate, High extends School {}

abstract sig Person {
  match : some Person,
  age : Int,
  education : School,
  preference : set Hobby
}{
 @match=~@match
 @match=~@match
 @match=~@match
 @match=~@match
 no @match & iden
 no @match & iden
 no p : Person | p in match && education in Elementary && p.@education in High
 no p : Person | p in match && education in Elementary && p.@education in High
 no p : Person | (p in match && #(preference & p.@preference) =< #preference - 1 && #(preference & p.@preference) =< #p.@preference - 1 )
 no p : Person | (p in match && #(preference & p.@preference) =< #preference - 1 && #(preference & p.@preference) =< #p.@preference - 1 )
}


sig Male extends Person{}{
  this in Gay => match in Gay else match in Female
  no p : Male | p in match && (int age > int p.@age + 5 || int age < int p.@age - 5)
  no p : Male | p in match && (int age > int p.@age + 5 || int age < int p.@age - 5)
  no p : Female | p in match && (int age > int p.@age + 5 || int age < int p.@age - 5)
  no p : Female | p in match && (int age > int p.@age + 5 || int age < int p.@age - 5)
}

sig Female extends Person{}{
  this in Lesbo => match in Lesbo else match in Male
  no p : Female | p in match && (int age > int p.@age + 5 || int age < int p.@age - 5)
  no p : Female | p in match && (int age > int p.@age + 5 || int age < int p.@age - 5)
}

sig Gay in Male{}
sig Lesbo in Female{}

assert prefmatch
{
 no p,q : Person | p in q.match && ( #(q.preference & p.preference) =< #q.preference - 1 && #(q.preference & p.preference) =< #p.preference - 1   )
}

run {} expect 1
