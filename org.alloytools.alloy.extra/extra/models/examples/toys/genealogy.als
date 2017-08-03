module examples/toys/genealogy

/*
 * Toy model of genealogical relationships
 *
 * The purpose of this model is to introduce basic concepts in Alloy.
 * The signature Person introduces a set of persons; this is paritioned into
 * two subsets, Man and Woman. The subsignature Adam declares a set of men
 * with one element -- that is, a scalar. Similarly, Eve declares a single
 * woman.
 *
 * The Person signature declares two fields: a person has one or zero spouses
 * and a set of parents.
 *
 * The facts should be self-explanatory. Note that the constraint that
 * spouse is a symmetric relation (that is, p is a spouse of q if q is a spouse
 * of p) is written by equating the field, viewed as a relation, to its
 * transpose. Since signatures have their own namespaces, and the same field
 * name can refer to different fields in different relations, it is necessary
 * to indicate which signature the field belongs to. This is not necessary when
 * dereferencing a field, because the appropriate field is automatically
 * determined by the type of the referencing expression.
 *
 * The command has no solutions. Given only 5 persons, it's not possible
 * to have a couple distinct from Adam and Eve without incest. To understand
 * the model, try weakening the constraints by commenting lines out (just
 * put two hyphens at the start of a line) and rerunning the command.
 *
 * author: Daniel Jackson, 11/13/01
 */

abstract sig Person {spouse: lone Person, parents: set Person}
sig Man, Woman extends Person {}
one sig Eve extends Woman {}
one sig Adam extends Man {}

fact Biology {
    -- nobody is his or her own ancestor
    no p: Person | p in p.^parents
    }

fact Bible {
    -- every person except Adam and Eve has a mother and father
    all p: Person - (Adam + Eve) | one mother: Woman, father: Man |
        p.parents = mother + father
    -- Adam and Eve have no parents
    no (Adam + Eve).parents
    -- Adam's spouse is Eve
    Adam.spouse = Eve
    }

fact SocialNorms {
    -- nobody is his or her own spouse
    no p: Person | p.spouse = p
    -- spouse is symmetric
    spouse = ~spouse
    -- a man's spouse is a woman and vice versa
    Man.spouse in Woman && Woman.spouse in Man
    }

fact NoIncest {
    -- can't marry a sibling
    no p: Person | some p.spouse.parents & p.parents
    -- can't marry a parent
    no p: Person | some p.spouse & p.parents
    }

pred Show {
    some p: Person - (Adam + Eve) | some p.spouse
    }
run Show for 6 expect 1



