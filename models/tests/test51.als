module tests/test51 -- example created by Emina Torlak on behalf of Mr. X

open tests/test51e as expansion

one sig M4, A34, A40 extends Road {}
one sig Oxford, OxfordW, Newbury, NewburyRoundabout, Burford, Swindon, Bicester extends Place {}
one sig a34b, a34o, a34n, a40o, a40b, m4s, m4n extends Point {}

fact GeographyStructure {
  (place    =   a34b->Bicester + a34o->Oxford + (a34n+m4n)->NewburyRoundabout +
            a40o->OxfordW + a40b->Burford + m4s->Swindon) and

 (Road.connections =    a40o->A34 + a34o->A40 + a40b->Swindon + (m4n+a34n)->Newbury) and

 (  M4.geography    =   0->m4s + 1->m4n and
    A34.geography   =   0->a34b + 1->a34o + 2->a34n and
    A40.geography   =   0->a40b + 1->a40o )
}

run { some Expansion<:next } for 4 but 4 seq, 3 Road, 7 Place, 7 Point, 3 Expansion expect 1
