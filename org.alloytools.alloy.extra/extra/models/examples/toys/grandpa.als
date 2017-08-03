module grandpa

/*
 * An Alloy model of the song "I Am My Own Grandpa"
 * by Dwight B. Latham and Moe Jaffe
 *
 * The challenge is to produce a man who is his own grandfather
 * without resorting to incest or time travel.  Executing the predicate
 * "ownGrandpa" will demonstrate how such a thing can occur.
 *
 * The full song lyrics, which describe an isomorophic solution,
 * are included at the end of this file.
 *
 * model author: Daniel Jackson
 */

abstract sig Person {
    father: lone Man,
    mother: lone Woman
    }

sig Man extends Person { wife: lone Woman }

sig Woman extends Person { husband: lone Man }

fact Biology { no p: Person | p in p.^(mother+father) }

fact Terminology { wife = ~husband }

fact SocialConvention {
    no wife & *(mother+father).mother
    no husband & *(mother+father).father
    }

fun grandpas [p: Person]: set Person {
    let parent = mother + father + father.wife + mother.husband |
        p.parent.parent & Man
    }

pred ownGrandpa [m: Man] { m in grandpas[m]  }

run ownGrandpa for 4 Person expect 1

/* defined variables:
 *
 * spouse = husband+wife
 */

/*
I Am My Own Grandpa
by Dwight B. Latham and Moe Jaffe

Many many years ago, when I was twenty-three,
I was married to a widow as pretty as can be,
This widow had a grown-up daughter who had hair of red,
My father fell in love with her and soon the two were wed.

    I'm my own grandpa, I'm my own grandpa.
    It sounds funny, I know, but it really is so—
    I'm my own grandpa.

This made my dad my son-in-law and changed my very life,
For my daughter was my mother, for she was my father's wife.
To complicate the matter, even though it brought me joy,
I soon became the father of a bouncing baby boy.

My little baby thus became a brother-in-law to dad,
And so became my uncle, though it made me very sad,
For if he was my uncle then that also made him brother
To the widow's grown-up daughter, who of course was my step-mother.

Father's wife then had a son who kept them on the run.
And he became my grandchild for he was my daughter's son.
My wife is now my mother's mother and it makes me blue,
Because although she is my wife, she's my grandmother, too.

Oh, if my wife's my grandmother then I am her grandchild.
And every time I think of it, it nearly drives me wild.
For now I have become the strangest case you ever saw—
As the husband of my grandmother, I am my own grandpa.

    I'm my own grandpa, I'm my own grandpa.
    It sounds funny, I know, but it really is so—
    I'm my own grandpa.
    I'm my own grandpa, I'm my own grandpa.
    It sounds funny, I know, but it really is so—
    I'm my own grandpa.
*/
