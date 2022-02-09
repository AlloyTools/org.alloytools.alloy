var sig V {}

t6: run { eventually V != V' } expect 1

t8: run { always V = V' } expect 1

t10: run { always eventually V = V' and always eventually V != V' } expect 1

----------------------------------------------------------------------
var lone sig W {}

t15: check { always lone W } expect 0

t17: run { eventually (some x: W | eventually some y: W | x != y) } expect 1

t19: run { some x: W | always W in x } expect 1

----------------------------------------------------------------------
var some sig Y {}

t24: check { always some Y } expect 0

t26: run { some x: Z | always Z in x } expect 1

----------------------------------------------------------------------
var one sig Z {}

t31: check { always lone Z } expect 0

t33: check { always some Z } expect 0

t35: check { always one Z } expect 0

t37: run { eventually (some x: Z | eventually some y: Z | x != y) } expect 1

t39: run { some x: Z | always Z in x } expect 1

----------------------------------------------------------------------
var sig A {}

var sig B, C extends A {}

t46: check { always B in A } expect 0

t48: check { always C in A } expect 0

t50: check { 
    always all x: B, y: C | always (x not in C and y not in B)
} expect 0

----------------------------------------------------------------------
var abstract sig D {}

var sig E, F extends D {}

t59: check { always D in E + F } expect 0

t61: check { always E in D } expect 0

t63: check { always F in D } expect 0

t65: check { 
    always all x: E, y: F | always (x not in F and y not in E)
} expect 0

----------------------------------------------------------------------

var sig G, H, I, J {}

pred p { some G }
pred q { some H }
pred r { some I }
pred s { some J }

pred tt { G = G }
pred ff { G != G }

t81: check { (always after p) iff (after always p) } expect 0

t83: check { always p iff not (eventually not p) } expect 0

t85: check { after ff iff ff } expect 0

t87: check { eventually ff iff ff } expect 0 

t89: check { (after p until q and r) iff (((after p) until q) and r) } expect 0

t91: check { (after tt) iff tt } expect 0
t92: check { (always ff) iff ff } expect 0

t94: check { (eventually tt) iff tt } expect 0
t95: check { (eventually eventually ff) iff eventually ff } expect 0

t97: check { (always tt) iff tt } expect 0
t98: check { (always always ff) iff always ff } expect 0

t100: check { (p until tt) iff tt } expect 0
t101: check { (ff until p) iff p } expect 0
t102: check { (p until ff) iff ff } expect 0
t103: check { (p until p) iff p } expect 0
t104: check { (tt until p) iff eventually p } expect 0
t105: check { ((after p) until (after q)) iff after (p until q) } expect 0

t107: check { (p releases q) iff not ((not p) until (not q)) } expect 0
t108: check { (p releases tt) iff tt } expect 0
t109: check { (p releases ff) iff ff } expect 0
t110: check { (tt releases p) iff p } expect 0
t111: check { (p releases p) iff p } expect 0
t112: check { (ff releases p) iff always p } expect 0
t113: check { (p releases q) iff (q and (p or after (p releases q))) } expect 0

t115: check { (after eventually always p) iff eventually always p } expect 0
t116: check { (after always eventually p) iff always eventually p } expect 0
t117: check { (after eventually p) iff eventually after p } expect 0

t119: check { (eventually (p until q)) iff eventually q } expect 0
t120: check { (eventually always (p and after q)) iff eventually always (p and q) } expect 0 
t121: check { (eventually always (p and always q)) iff eventually always (p and q) } expect 0
t122: check { (eventually always (p or always q)) iff eventually (always p or always q) } expect 0
t123: check { (eventually always (p and eventually q)) iff ((eventually always p) and always eventually q) } expect 0
t124: check { (eventually always (p or eventually q)) iff ((eventually always p) or always eventually q) } expect 0

t126: check { (always eventually (p or after q)) iff always eventually (p or q) } expect 0
t127: check { (always eventually (p or eventually q)) iff always eventually (p or q) } expect 0
t128: check { (always eventually (p and eventually q)) iff always (eventually p and eventually q) } expect 0
t129: check { (always eventually (p and always q)) iff ((always eventually p) and eventually always q) } expect 0
t130: check { (always eventually (p or always q)) iff ((always eventually p) or eventually always q) } expect 0

t132: check { (p until always p) iff always p } expect 0
t133: check { (p releases (eventually p)) iff eventually p } expect 0


t136: check { (eventually always p and eventually always q) iff eventually always (p and q) } expect 0
t137: check { (after p and after q) iff after (p and q) } expect 0
t138: check { (after p and eventually always q) iff after (p and eventually always q) } expect 0
t139: check { ((p until q) and (r until q)) iff ((p and r) until q) } expect 0
t140: check { ((p releases q) and (p releases r)) iff (p releases (q and r)) } expect 0
t141: check { ((p until q) or (p until r)) iff (p until (q or r)) } expect 0
t142: check { ((p releases q) or (r releases q)) iff ((p or r) releases q) } expect 0

t144: check { ((always q) or (p releases q)) iff (p releases q) } expect 0


t147: check { ((after p) releases (after q)) iff after (p releases q) } expect 0

t149: check { (always (p releases q)) iff always q } expect 0 

t151: check { eventually always once p iff eventually p } expect 0