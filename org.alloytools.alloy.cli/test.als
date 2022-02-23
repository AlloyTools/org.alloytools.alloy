some sig A,B {
    x : set Int
}

fact {
    #A = 3
    #B = 3
    
}
pred rel[ r : A lone -> lone B ] { 
    all a: A | lone a.r 
    all b: B | lone r.b 
}

run rel