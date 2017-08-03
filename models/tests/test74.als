module tests/test

open util/integer

sig LongString, Email, Date, DateTime { }

enum Stringz { StringAlex, StringBrian, StringEmina, StringDaniel, StringFelix, StringIan, StringJukka,
              StringMIT, StringNokia, StringWindowsDiscussion, StringLinuxDiscussion,
              StringMachineLearning, StringNumericOptimization, StringTrueMultithreading, StringEfficientCompilerConstruction,
              StringHowToOptimize, StringHelpNeeded }

enum Boolean { True, False }

abstract sig Entity {
  owners: set Entity,
  created: DateTime,
  lastModified: DateTime
}

one sig me in Entity { }

abstract sig LoginUser extends Entity { suspended: Boolean,  email: disjoint Email,  password: Stringz } // magic GUI support

one sig ADD1, ADD2, DELETE1, DELETE2 { }
enum Action { R, A, D, AS, DS }
fun W: set Action  { A+D }
fun RW: set Action { R+W }
let ADD = ADD1->ADD2
let DELETE = DELETE1->DELETE2

fun own: set Entity { Entity }

fun policy : univ -> univ -> univ
{
 R -> me -> (LoginUser$email + User$getMail)
 + (A+D) -> (me.super=True => Entity else none) -> field$
 + (R+A+D) -> own -> (field$ - Entity$owners - Entity$created - Entity$lastModified - User$super - LoginUser$suspended - Topic$replies - Topic$pinned - Topic$readOnly)
 + DS -> Group -> Group$members
 + ADD -> (me.super=True => (User$ + Group$ + Talk$ + Forum$ + Topic$ + Msg$) else (Group$ + Talk$ + Topic$ + Msg$))
 + DELETE -> own
}

sig User extends LoginUser {
    name    : disjoint Stringz,
    bio     : lone LongString,
    super   : Boolean,
    getMail : Boolean
}

fun User.groups : set Group { members.(user.this) }
fun User.points : Int       { 25.mul[#(Talk<:owners . this)] + 20.mul[#(Msg<:owners . this)]  }

---------------------------------------------------------------------------------------------------------------------------------------------------------

sig Group extends Entity {
    name       : disjoint Stringz,
    descr      : lone LongString,
    homeMsg    : lone LongString,
    restricted : Boolean,
    members    : set Member
}

fun Group.admins : set User { (type.GroupAdmin & this.members).user }

sig Member { user: disjoint User, type: Type }

enum Type { GroupAdmin, Regular, Tentative }

pred members.onAdd {
  let g=this.univ, u=univ.this.user, t=univ.this.type {
     me !in g.admins => (u=me && (g.restricted=False => t=Regular else t=Tentative))
  }
}

sig Talk extends Entity {
    title    : Stringz,
    datetime : DateTime,
    location : lone LongString,
    descr    : lone LongString,
    speakers : some Stringz,
    tags     : set Group
} {
    tags in owners.groups
}

sig Forum extends Entity {
    name     : disjoint Stringz,
    descr    : lone LongString,
    weight   : Int,
    readOnly : Boolean,
    topics   : set Topic
}

fun Forum.numTopics : Int { #(this.topics) }
fun Forum.numText   : Int { #(this.topics) + #(this.topics.replies) }

sig Topic extends Entity {
    title    : Stringz,
    text     : LongString,
    pinned   : Boolean,
    readOnly : Boolean,
    replies  : set Msg
}

fun Topic.parent      : Forum    { topics.this     }
fun Topic.numReplies  : Int      { #(this.replies) }
fun Topic.firstAuthor : User     { this.owners     }
fun Topic.firstDate   : DateTime { this.created    }
pred Topic.onAdd { me.super = True || this.pinned + this.readOnly + this.parent.readOnly = False }

sig Msg extends Entity { text : LongString }
fun Msg.parent : Topic { replies.this }
pred Msg.onAdd {  me.super = True || this.parent.readOnly = False }

run {
let namez = StringAlex + StringBrian + StringEmina + StringDaniel + StringFelix + StringIan + StringJukka |
let groupz = StringMIT + StringNokia |
let forumz = StringWindowsDiscussion + StringLinuxDiscussion |
let talkz = StringMachineLearning + StringNumericOptimization + StringTrueMultithreading + StringEfficientCompilerConstruction |
let topicz = StringHowToOptimize + StringHelpNeeded |
{
(!lone User)
(all x:Entity | some x.owners)
(all x:Entity | x.owners in User)
(all x:User | some x.bio && x.name in namez && some x.groups)
(all x:Group | some x.descr && some x.homeMsg && some {g:x.members | g.type=GroupAdmin} && some {g:x.members | g.type=Regular} && some {g:x.members | g.type=Tentative} && x.name in groupz)
(all x:Talk | some x.location)
(all x:Talk | some x.descr)
(all x:Talk | some x.tags)
(all x:Talk | x.title in talkz)
(all x:Forum | some x.descr && x.name in forumz)
(all x:Topic | x.title in topicz)
(all disj x, y: Topic | x.title != y.title)
(all disj x, y: Talk | x.title != y.title)
(all disj x, y: Msg | x.text != y.text)
}
} for 7 but 1 DateTime, exactly 7 User, exactly 2 Group, exactly 4 Talk, exactly 2 Forum, exactly 2 Topic, exactly 4 Msg expect 1
