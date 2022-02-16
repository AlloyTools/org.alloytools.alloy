some sig Foo {
}
pred foo[ a, b, abh, bah : set Foo, ab, ba : Foo->Foo] {
   ab=a->b
   ba=b->a
   abh=ab.univ
   bah=ba.univ
} 
