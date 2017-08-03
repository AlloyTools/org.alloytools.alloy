module examples/puzzles/handshake

/*
 * Alloy model of the Halmos handshake problem
 *
 * Hilary and Jocelyn are married. They invite four couples who are friends for dinner. When
 * they arrive, they shake hands with each other. Nobody shakes hands with him or herself
 * or with his or her spouse. After there has been some handshaking, Jocelyn jumps up on
 * a chair and says "Stop shaking hands!", and then asks how many hands each person has
 * shaken. All the answers are different. How many hands has Hilary shaken?
 *
 * The Alloy model represents the problem as a set of constraints. Properties of the spouse
 * relationship and of handshaking in general are given as facts. The particular situation
 * is cast as a function.
 *
 * There are 9 people answering, and all answers are different. Nobody can shake more than
 * 8 hands. So answers must be 0..8. The one (p8 say) who answered 8 has shaken everybody's
 * hand except for his or her own, and his or her spouse's. Now consider the person who shook
 * 0 hands (p0 say). The persons p0 and p8 are distinct. If they are not married, then p8 cannot
 * have shaken 8 hands, because he or she did not shake the hand of p0 or of his or her spouse.
 * So p8's spouse to p0. Now imagine Jocelyn asking the question again, with p0 and p8 out of
 * the room, and excluding hand shakes with them. Since p8 shook hands with everyone else
 * except p0 and p8, everyone gives an answer one smaller than they did before, giving 0..6.
 * The argument now applies recursively. So Hilary is left alone, having shaken 4 hands.
 *
 * author: Daniel Jackson, 11/15/01
 */

sig Person {spouse: Person, shaken: set Person}
one sig Jocelyn, Hilary extends Person {}

fact ShakingProtocol {
    // nobody shakes own or spouse's hand
    all p: Person | no (p + p.spouse) & p.shaken
    // if p shakes q, q shakes p
    all p, q: Person | p in q.shaken => q in p.shaken
    }

fact Spouses {
    all p, q: Person | p!=q => {
        // if q is p's spouse, p is q's spouse
        p.spouse = q => q.spouse = p
        // no spouse sharing
        p.spouse != q.spouse
        }
    all p: Person {
        // a person is his or her spouse's spouse
        p.spouse.spouse = p
        // nobody is his or her own spouse
        p != p.spouse
        }
    }

pred Puzzle {
    // everyone but Jocelyn has shaken a different number of hands
    all p,q: Person - Jocelyn | p!=q => #p.shaken != #q.shaken
    // Hilary's spouse is Jocelyn
    Hilary.spouse = Jocelyn
    }

P10: run Puzzle for exactly 10 Person, 5 int expect 1
P12: run Puzzle for exactly 12 Person, 5 int expect 1
P14: run Puzzle for exactly 14 Person, 5 int expect 1
P16: run Puzzle for exactly 16 Person, 6 int expect 1
