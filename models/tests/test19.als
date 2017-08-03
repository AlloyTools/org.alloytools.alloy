module tests/test // Bugpost by g.a.c.rijnders@gmail.com

open util/integer as integer

one sig JochemVanGelder extends Human{}{
    sports in interests
    matchtype= Woman
    sex=Man
}

abstract sig Human {
    interests: set Interest ,
    matchtype: set Sex,
    match: set Human,
    level: one KnowledgeLevel,
    age: one Int,
    sex: Sex
}

abstract sig KnowledgeLevel{}
one sig dumb extends KnowledgeLevel{}

abstract sig Interest{}
one sig sports extends Interest {}

abstract sig Sex{}
one sig Man extends Sex{}
one sig Woman extends Sex{}

pred isGay(h:Human){
    h.sex = h.matchtype
}

pred isStraight(h:Human){
    h.sex !in h.matchtype
}

pred isBi(h:Human){
    not isStraight[h] && not isGay[h]
}

fact {
    some h:Human | isBi[h]
}

pred couple(h1:Human,h2:Human){
    /* don't date yourself */
    h1 != h2

    /* minimal 2 shared interest*/
    && #(h1.interests & h2.interests) >= 2

    /* match sexual preference */
     && h1.sex in h2.matchtype
     && h2.sex in h1.matchtype
    /* ^ this does allow for a bisexual person to match with a straight */

    /* Similar level of education (distinguish three levels).*/
    && h1.level = h2.level
}

/* some man dating a Bi woman which is dating another woman */
/* or */
/* some woman dating a Bi man which is dating another man */
pred luckyMen(){
    some h1,h2,h3:Human | isStraight[h1] && isBi[h2] && h2 in h1.match && h3 in h2.match && h3.sex in h1.matchtype
}

/* is there a chain of people liking eachother ? */
pred group{
    some h:Human | h in h.^match
}

pred show(){}

fun diff( n1,n2: Int) : Int{
    int n1 > int n2 implies sub[ n1, n2 ]
                         else sub[ n2, n1 ]
}


fun diff2( n1,n2: Int) : Int{
    gte[ n1 , n2] implies sub[ n1, n2 ]
                         else sub[ n2, n1 ]
}

assert vreemd{
    all h:Human | h.match.sex in h.matchtype
}
check vreemd for 5 int expect 0

// Facts

fact def{
    all a:Human |
            /* someone should have atleast one prefered sex to date*/
            #a.matchtype > 0 &&
            /* Fill interests */
             #a.interests >=2 &&
            /* Basic age rules */
            gte[a.age, Int [0] ]
}

fact def2{
    /* Fill matches*/
    all h1,h2:Human|
        couple[h1,h2] <=> h1 in h2.match /* && h2 in h1.match   */
}

run show for 3 int expect 0
run luckyMen for 3 int expect 0
run group for 3 int expect 0

run show for 2 int expect 0
run luckyMen for 2 int expect 0
run group for 2 int expect 0
