module tests/test // Problem reported by Manachai Toahchoodee

sig Role { }
sig Session{}
fact NoIdleSession { all a:Session | some b,c:Role | some a->b->c }
x: check { some Role } for 1 Role, 2 Session, 2 int expect 1
