module tests/test // Problem reported by Manachai Toahchoodee

sig Time{}
sig Location{}
sig User{}
sig Role{
    RoleAllocLoc: Location,
    RoleAllocDur: Time,
    RoleEnableLoc: Location,
    RoleEnableDur: Time}
sig Permission{}
sig Object{}
sig Session{}
sig sType{}

one sig RoleEnable {member : Role-> Time ->Location}
one sig RolePermissionAssignment{member : Role-> Permission ->Time->Location}
one sig UserLocation{member : User->Time->Location}
one sig ObjLocation{member : Object->Time->Location}
one sig UserRoleAssignment{member : User-> Role->Time->Location}
one sig UserRoleActivate{member : User-> Role->Time->Location}
one sig RoleHierarchy{RHmember : Role -> Role}
one sig SessionType{member : Session->sType}
one sig SessionLoc{member : sType->Location}
one sig SessionUser{member : Session-> one User ->Time}
one sig SessionRole{member : Session->Role->Time->Location}
one sig PermRoleLoc{member : Permission->Role->Location}
one sig PermDur{member : Permission->Time}
one sig PermRoleAcquire{member : Permission -> Role ->Time ->Location}

fact ULoc{
    all u: User, uloc: UserLocation, d: Time, l1, l2: Location |
        (((u->d->l1) in uloc.member) && ((u->d->l2) in uloc.member)) <=>
            ((l1 in l2) || (l2 in l1))}
fact ObjLoc{
    all o: Object, oloc: ObjLocation, d: Time, l1, l2: Location |
        (((o->d->l1) in oloc.member) && ((o->d->l2) in oloc.member)) <=>
            ((l1 in l2) || (l2 in l1))}
fact URAssign{
    all u: User, r: Role, d: Time, l: Location, ura: UserRoleAssignment, uloc: UserLocation |
        ((u->r->d->l) in ura.member) => (((u->d->l) in uloc.member) &&
            (l in r.RoleAllocLoc) && (d in r.RoleAllocDur))}
fact URActivate{
    all u: User, r: Role, d: Time, l: Location, uras: UserRoleAssignment, urac: UserRoleActivate |
        ((u->r->d->l) in urac.member) => (((u->r->d->l) in uras.member) &&
            (l in r.RoleEnableLoc) && (d in r.RoleEnableDur))}
fact NocycleRH{
    all r: Role, RH: RoleHierarchy| r !in r.^(RH.RHmember)}

//Every Session has an owner
fact NoIdleSession{
    all s: Session | some u: User, d : Time, su : SessionUser |
        s->u->d in su.member
}

fact SessionUserFact{
    all s: Session, u: User, d: Time, su: SessionUser, ul: UserLocation,
    sl : SessionLoc, st : SessionType |
        (s->u->d in su.member) => ((ul.member[u])[d] in sl.member[st.member[s]])
}

//Session Role relationship must has its owner (Session User)
fact SessionRoleFact1{
    all s: Session | some u: User, r: Role, d: Time, l: Location, sr: SessionRole,
    su : SessionUser |
        (s->r->d->l in sr.member) =>
            (s->u->d in su.member)
}

fact SessionRoleFact2{
    all s: Session| some u: User, r: Role, d: Time, l: Location, sr: SessionRole,
    su: SessionUser, sl : SessionLoc, st : SessionType |
        ((s->r->d->l in sr.member) && (s->u->d in su.member)) =>
            ((u->r->d->l in UserRoleActivate.member) && (l in sl.member[st.member[s]]))
}

fact PermRoleAcquireFact{
    all p: Permission, r: Role, d: Time, l: Location, pra: PermRoleAcquire,
    prl : PermRoleLoc, pd : PermDur |
        (p->r->d->l in pra.member) => ((l in ((prl.member[p])[r] & r.RoleEnableLoc)) &&
        (d in (pd.member[p] & r.RoleEnableDur)))
}




// Functions
//Unrestricted Permission Inheritance Hierarchy
fun UPIHPermAcquire(sr: Role): RolePermissionAssignment.member{
    (sr->(sr.(RoleHierarchy.RHmember)).(RolePermissionAssignment.member).Location.Time->sr.RoleEnableDur->sr.RoleEnableLoc) ++
    (sr <: RolePermissionAssignment.member)}


// Predicates
//Weak Form of SSoD-User Role Assignment
pred W_SSoD_URA(u: User, disj r1, r2: Role, ura: UserRoleAssignment.member, d: Time, l: Location){
        ((u->r1->d->l) in ura) => ((u->r2->d->l) not in ura)}

// Conflicts with the Weak Form of SSOD-User Role Assignment: Condition 1
assert TestConflict1_1{
    all u: User, x, y: Role, RH: RoleHierarchy, d: Time, l: Location,
    ura: UserRoleAssignment |
        ((x -> y in RH.RHmember) && (u->x->d->l in ura.member)) =>
            W_SSoD_URA[u, x, y, u->(x+y)->d->l, d, l]
}
check TestConflict1_1 expect 1
