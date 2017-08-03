/* Copyright 2010-2011 Armin Biere Johannes Kepler University Linz Austria */

#include "lglib.h"
#ifndef NLGLPICOSAT
#include "picosat.h"
#endif
#include <assert.h>
#include <limits.h>
#include <math.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <sys/resource.h>
#include <sys/time.h>
#include <unistd.h>

#define REMOVED		INT_MAX
#define NOTALIT		((INT_MAX >> RMSHFT))
#define MAXVAR		((INT_MAX >> RMSHFT) - 2)
#define MAXSCOREXP	(1<<24)
#define SCINCMINEXP	(-(1<<24))
#define GLUESHFT	4
#define POW2GLUE	(1 << GLUESHFT)
#define MAXGLUE		(POW2GLUE-1)
#define GLUEMASK	(POW2GLUE - 1)
#define MAXREDLIDX	((1 << (31 - GLUESHFT)) - 2)
#define MAXIRRLIDX	((1 << (31 - RMSHFT)) - 2)
#define FLTPRC 		32
#define EXPMIN 		(0x0000 ## 0000)
#define EXPZRO 		(0x1000 ## 0000)
#define EXPMAX		(0x7fff ## ffff)
#define MNTBIT		(0x0000 ## 0001 ## 0000 ## 0000 ## ull)
#define MNTMAX		(0x0000 ## 0001 ## ffff ## ffff ## ull)
#define FLTMIN		(0x0000 ## 0000 ## 0000 ## 0000 ## ll)
#define FLTMAX		(0x7fff ## ffff ## ffff ## ffff ## ll)
#define MAXLDFW		31	
#define REPMOD 		23
#define MAXFLTSTR	2
#define MAXPHN		3
#define FALSECNF	(1ll<<32)
#define TRUECNF		0ll
#define FUNVAR		11
#define FUNQUADS	(1<<(FUNVAR - 6))
#define MINPEN		0
#define MAXPEN		4

#define cover(b) assert(!(b))

typedef enum Tag {
  FREEVAR = 0,
  FIXEDVAR = 1,
  EQUIVAR = 2,
  ELIMVAR = 3,

  DECISION = 0,
  UNITCS = 1,
  IRRCS = 1,
  BINCS = 2,
  TRNCS = 3,
  LRGCS = 4,
  MASKCS = 7,

  REDCS = 8,
  RMSHFT = 4,
} Tag;

#define COVER(COVER_CONDITION) \
do { \
  if (!(COVER_CONDITION)) break; \
  fprintf (stderr, \
           "c *LGLIB* covered line %d: %s\n", \
	   __LINE__, # COVER_CONDITION); \
  if (getenv("LGLNCOVER")) break; \
  abort (); /* NOTE: not 'lglabort' on purpose */ \
} while (0)

#define MAPLOGLEVEL(LEVEL) (LEVEL)

/*
#undef MAPLOGLEVEL
#define MAPLOGLEVEL(LEVEL) 0
#undef MAPLOGLEVEL
#define MAPLOGLEVEL(LEVEL) (LEVEL)
*/

#ifndef NLGLOG
#define LOG(LEVEL,FMT,ARGS...) \
  do { \
    if (MAPLOGLEVEL(LEVEL) > lgl->opts.log.val) break; \
    lglogstart (lgl, MAPLOGLEVEL(LEVEL), FMT, ##ARGS); \
    lglogend (lgl); \
  } while (0)
#define LOGCLS(LEVEL,CLS,FMT,ARGS...) \
  do { \
    const int * P; \
    if (MAPLOGLEVEL(LEVEL) > lgl->opts.log.val) break; \
    lglogstart (lgl, MAPLOGLEVEL(LEVEL), FMT, ##ARGS); \
    for (P = (CLS); *P; P++) printf (" %d", *P); \
    lglogend (lgl); \
  } while (0)
#define LOGMCLS(LEVEL,CLS,FMT,ARGS...) \
  do { \
    const int * P; \
    if (MAPLOGLEVEL(LEVEL) > lgl->opts.log.val) break; \
    lglogstart (lgl, MAPLOGLEVEL(LEVEL), FMT, ##ARGS); \
    for (P = (CLS); *P; P++) printf (" %d", lglm2i (lgl, *P)); \
    lglogend (lgl); \
  } while (0)
#define LOGRESOLVENT(LEVEL,FMT,ARGS...) \
  do { \
    const int * P; \
    if (MAPLOGLEVEL(LEVEL) > lgl->opts.log.val) break; \
    lglogstart (lgl, MAPLOGLEVEL(LEVEL), FMT, ##ARGS); \
    for (P = lgl->resolvent.start; P < lgl->resolvent.top; P++) \
      printf (" %d", *P); \
    lglogend (lgl); \
  } while (0)
#define LOGREASON(LEVEL,LIT,REASON0,REASON1,FMT,ARGS...) \
  do { \
    int TAG, TMP, RED, G; \
    const int * C, * P; \
    if (MAPLOGLEVEL(LEVEL) > lgl->opts.log.val) break; \
    lglogstart (lgl, MAPLOGLEVEL(LEVEL), FMT, ##ARGS); \
    TMP = (REASON0 >> RMSHFT); \
    RED = (REASON0 & REDCS); \
    TAG = (REASON0 & MASKCS); \
    if (TAG == DECISION) fputs (" decision", stdout); \
    else if (TAG == UNITCS) printf (" unit %d", LIT); \
    else if (TAG == BINCS) { \
      printf (" %s binary clause %d %d", lglred2str (RED), LIT, TMP); \
    } else if (TAG == TRNCS) { \
      printf (" %s ternary clause %d %d %d", \
              lglred2str (RED), LIT, TMP, REASON1); \
    } else { \
      assert (TAG == LRGCS); \
      C = lglidx2lits (lgl, RED, REASON1); \
      for (P = C; *P; P++) \
	; \
      printf (" size %ld", (long)(P - C)); \
      if (RED) { \
	G = (REASON1 & GLUEMASK); \
	printf (" glue %d redundant", G); \
      } else fputs (" irredundant", stdout); \
      fputs (" clause", stdout); \
      for (P = C; *P; P++) { \
	printf (" %d", *P); \
      } \
    } \
    lglogend (lgl); \
  } while (0)
#define LOGDSCHED(LEVEL,LIT,FMT,ARGS...) \
  do { \
    int POS; Scr SCORE; \
    if (MAPLOGLEVEL(LEVEL) > lgl->opts.log.val) break; \
    POS = *lgldpos (lgl, LIT); \
    SCORE = lglavar (lgl, LIT)->score; \
    lglogstart (lgl, MAPLOGLEVEL(LEVEL), "dsched[%d] = %d ", POS, LIT); \
    printf (FMT, ##ARGS); \
    printf (" score "); \
    printf ("%s", lglflt2str (lgl, SCORE)); \
    lglogend (lgl); \
  } while (0)
#define LOGESCHED(LEVEL,LIT,FMT,ARGS...) \
  do { \
    int POS; int SCORE; \
    EVar * EV; \
    if (MAPLOGLEVEL(LEVEL) > lgl->opts.log.val) break; \
    POS = *lglepos (lgl, LIT); \
    SCORE = lglescore (lgl, LIT); \
    lglogstart (lgl, MAPLOGLEVEL(LEVEL), "esched[%d] = %d ", POS, LIT); \
    printf (FMT, ##ARGS); \
    EV = lglevar (lgl, LIT); \
    printf (" score %d occ %d %d", SCORE, EV->occ[0], EV->occ[1]); \
    lglogend (lgl); \
  } while (0)
#define LOGFLT(LEVEL,FLT,FMT,ARGS...) \
  do { \
    int EXP; Mnt MNT; \
    if (MAPLOGLEVEL(LEVEL) > lgl->opts.log.val) break; \
    lglogstart (lgl, MAPLOGLEVEL(LEVEL), FMT, ##ARGS); \
    EXP = lglexp (FLT); \
    MNT = lglmnt (FLT); \
    printf (" %s %e %d %llu %016llx", \
            lglflt2str (lgl, FLT), lglflt2dbl (FLT), EXP, MNT, FLT); \
    lglogend (lgl); \
  } while (0)
#else
#define LOG(ARGS...) do { } while (0)
#define LOGCLS(ARGS...) do { } while (0)
#define LOGMCLS(ARGS...) do { } while (0)
#ifndef NDEBUG
#define LOGRESOLVENT(ARGS...) do { } while (0)
#endif
#define LOGREASON(ARGS...) do { } while (0)
#define LOGDSCHED(ARGS...) do { } while (0)
#define LOGESCHED(ARGS...) do { } while (0)
#define LOGFLT(ARGS...) do { } while (0)
#endif

#define ABORTIF(COND,FMT,ARGS...) \
  do { \
    if (!(COND)) break; \
    fprintf (stderr, \
             "*** API usage error of '%s' in '%s': ", \
             __FILE__, __FUNCTION__); \
    fprintf (stderr, FMT, ##ARGS); \
    fputc ('\n', stderr); \
    lglabort (lgl); \
  } while (0)

#define REQUIRE(STATE) \
  do { \
    ABORTIF (!lgl, "uninitialized manager"); \
    ABORTIF(!(lgl->state & (STATE)), "!(%s)", #STATE); \
  } while (0)

#define TRANS(STATE) \
do { \
  assert (lgl->state != STATE); \
  LOG (1, "transition to state " #STATE); \
  lgl->state = STATE; \
} while (0)

#define SWAP(A,B) do { typeof(A) TMP = (A); (A) = (B); (B) = TMP; } while (0)

#define NEW(P,N) \
  do { (P) = lglmalloc (lgl, (N) * sizeof *(P)); } while (0)
#define DEL(P,N) \
  do { lglfree (lgl, (P), (N) * sizeof *(P)); (P) = 0; } while (0)
#define RSZ(P,O,N) \
  do { (P) = lglrealloc (lgl, (P), (O)*sizeof*(P), (N)*sizeof*(P)); } while (0)
#define CLN(P,N) \
  do { memset ((P), 0, (N) * sizeof *(P)); } while (0)
#define CLRPTR(P) \
  do { memset ((P), 0, sizeof *(P)); } while (0)
#define CLR(P) \
  do { memset (&(P), 0, sizeof (P)); } while (0)

#define ISORTLIM 10
#define CMPSWAP(CMP,P,Q) \
  do { if ((CMP) (&(P), &(Q)) > 0) SWAP (P, Q); } while(0)
#define QPART(CMP,A,L,R) \
  do { \
    typeof(*(A)) PIVOT; \
    int J = (R); \
    I = (L) - 1; \
    PIVOT = (A)[J]; \
    for (;;) { \
      while ((CMP) (&(A)[++I], &PIVOT) < 0) \
	; \
      while ((CMP) (&PIVOT, &(A)[--J]) < 0) \
	if (J == (L)) break; \
      if (I >= J) break; \
      SWAP ((A)[I], (A)[J]); \
    } \
    SWAP ((A)[I], (A)[R]); \
  } while(0)
#define QSORT(CMP,A,N) \
  do { \
    int L = 0, R = (N) - 1, M, LL, RR, I; \
    assert (lglmtstk (&lgl->sortstk)); \
    if (R - L <= ISORTLIM) break; \
    for (;;) { \
      M = (L + R) / 2; \
      SWAP ((A)[M], (A)[R - 1]); \
      CMPSWAP (CMP, (A)[L], (A)[R - 1]); \
      CMPSWAP (CMP, (A)[L], (A)[R]); \
      CMPSWAP (CMP, (A)[R - 1], (A)[R]); \
      QPART (CMP, (A), L + 1, R - 1); \
      if (I - L < R - I) { LL = I + 1; RR = R; R = I - 1; } \
      else { LL = L; RR = I - 1; L = I + 1; } \
      if (R - L > ISORTLIM) { \
	assert (RR - LL > ISORTLIM); \
	lglpushstk (lgl, &lgl->sortstk, LL); \
	lglpushstk (lgl, &lgl->sortstk, RR); \
      } else if (RR - LL > ISORTLIM) L = LL, R = RR; \
      else if (!lglmtstk (&lgl->sortstk)) { \
	R = lglpopstk (&lgl->sortstk); \
	L = lglpopstk (&lgl->sortstk); \
      } else break; \
    } \
  } while (0)
#define ISORT(CMP,A,N) \
  do { \
    typeof(*(A)) PIVOT; \
    int L = 0, R = (N) - 1, I, J; \
    for (I = R; I > L; I--) \
      CMPSWAP (CMP, (A)[I - 1], (A)[I]); \
    for (I = L + 2; I <= R; I++) { \
      J = I; \
      PIVOT = (A)[I]; \
      while ((CMP) (&PIVOT, &(A)[J - 1]) < 0) { \
	(A)[J] = (A)[J - 1]; \
	J--; \
      } \
      (A)[J] = PIVOT; \
    } \
  } while (0)
#ifdef NDEBUG
#define CHKSORT(CMP,A,N) do { } while(0)
#else
#define CHKSORT(CMP,A,N) \
  do { \
    int I; \
    for (I = 0; I < (N) - 1; I++) \
      assert ((CMP) (&(A)[I], &(A)[I + 1]) <= 0); \
  } while(0)
#endif
#define SORT(A,N,CMP) \
  do { \
    typeof((A)) AA = (A); \
    int NN = (N); \
    QSORT (CMP, AA, NN); \
    ISORT (CMP, AA, NN); \
    CHKSORT (CMP, AA, NN); \
  } while (0)

typedef struct Opt {
  char shrt;
  const char * lng, * descrp;
  int val, min, max;
} Opt;

typedef struct Opts {
  Opt beforefirst;
  Opt acts;
  Opt actavgmax;
  Opt actstdmin;
  Opt actstdmax;
  Opt agile;
  Opt bias;
  Opt block;
  Opt blkclslim;
  Opt blkmaxeff;
  Opt blkmineff;
  Opt blkreleff;
  Opt blkocclim;
  Opt caplen;
#ifndef NDEBUG
  Opt check;
#endif
  Opt deactivate;
  Opt decompose;
  Opt dcpirrintinc;
  Opt dcpcintinc;
  Opt dcpvintinc;
  Opt defragint;
  Opt defragfree;
  Opt distill;
  Opt dstirrintinc;
  Opt dstcintinc;
  Opt dstvintinc;
  Opt dstmaxeff;
  Opt dstmineff;
  Opt dstreleff;
  Opt elim;
  Opt elmirrintinc;
  Opt elmcintinc;
  Opt elmvintinc;
  Opt elmclslim;
  Opt elmhte;
  Opt elmhtelim;
  Opt elmaxeff;
  Opt elmineff;
  Opt elmreleff;
  Opt elmreslim;
  Opt elmocclim;
  Opt elmnostr;
  Opt exitonabort;
  Opt gcirrintinc;
  Opt gccintinc;
  Opt gcvintinc;
  Opt gluescale;
  Opt hlaminlim;
  Opt hlamaxlim;
  Opt hlaliminc;
  Opt hte;
  Opt htered;
  Opt htemaxeff;
  Opt htemineff;
  Opt htereleff;
  Opt keepmaxglue;
  Opt lhbr;
  Opt lift;
  Opt lftirrintinc;
  Opt lftcintinc;
  Opt lftvintinc;
  Opt lftmaxeff;
  Opt lftmineff;
  Opt lftreleff;
#ifndef NLGLOG
  Opt log;
#endif
  Opt minlim;
  Opt otfs;
  Opt partition;
  Opt partcintinc;
  Opt partvintinc;
  Opt phase;
  Opt plain;
  Opt probe;
  Opt prbirrintinc;
  Opt prbcintinc;
  Opt prbvintinc;
  Opt prbmaxeff;
  Opt prbmineff;
  Opt prbreleff;
  Opt seed;
  Opt smallve;
  Opt smallvevars;
  Opt randec;
  Opt randecint;
  Opt rebias;
  Opt rebint;
  Opt rebflip;
  Opt rephrase;
  Opt rphrint;
  Opt rphrfac;
  Opt redlexpinc;
  Opt redlexpfac;
  Opt redlinit;
  Opt redlinc;
  Opt redlmininc;
  Opt redlmaxinc;
  Opt restart;
  Opt restartint;
  Opt restartype;
  Opt scincinc;
  Opt syncint;
  Opt termint;
  Opt transred;
  Opt trdirrintinc;
  Opt trdcintinc;
  Opt trdvintinc;
  Opt trdmineff;
  Opt trdmaxeff;
  Opt trdreleff;
  Opt unhide;
  Opt unhdextstamp;
  Opt unhdhbr;
  Opt unhdirrintinc;
  Opt unhdcintinc;
  Opt unhdvintinc;
  Opt unhdmaxeff;
  Opt unhdmineff;
  Opt unhdreleff;
  Opt unhdlnpr;
  Opt unhdroundlim;
  Opt verbose;
  Opt witness;
  Opt afterlast;
} Opts;

#define FIRSTOPT(lgl) (&(lgl)->opts.beforefirst + 1)
#define LASTOPT(lgl) (&(lgl)->opts.afterlast - 1)

typedef struct Stats {
  int defrags, iterations, rephrased;
  struct { int vars, clauses; } rescored;
  struct { int count, skipped; } rebias;
  struct { int count, skipped; 
           struct { int count; double sum; } kept; } restarts;
  struct { int count, geom, arith; } reduced;
  int acts, reported, gcs;
  int irr, decomps, lifted, simps;
  int64_t prgss, enlwchs, rdded, ronflicts, pshwchs, height;
  int64_t confs, decisions, randecs, uips;
  struct { int64_t sat, deref, freeze, melt, add, assume; } calls;
  struct { int64_t search, hits; } poison;
  struct { int64_t search, simp; } props, visits;
  struct { size_t current, max; } bytes;
  struct { int bin, trn, lrg; } red;
  struct { int cnt, trn, lrg, sub; } hbr;
  struct { int current, sum; } fixed, equiv;
  struct {
    struct { double process, phase[MAXPHN], * ptr[MAXPHN];
             int nesting; } entered;
    double all; } time;
  struct { int rounds, clauses, lits; int64_t res; } blk;
  struct { int count, failed;
           struct { struct { int lrg, trn; } irr, red; } taut, rem;
	   struct { int64_t steps; } hla, cls, all; } hte;
  struct { int count, red, failed, str; } dst;
  struct { int count, failed, lifted; int64_t probed; } prb;
  struct { int count, eqs, units, impls; int64_t probed[2]; } lift;
  struct { int count, red, failed; int64_t lits, bins, steps; } trd;
  struct { int removed, red; } bindup;
  struct { int count, rounds;
	   struct { int trds, failed, sccs; int64_t sumsccsizes; } stamp;
           struct { int lits, bin, trn, lrg; } failed;
           struct { int bin, trn, lrg, red; } tauts;
           struct { int bin, trn, lrg; } units;
           struct { int trn, lrg, red; } hbrs;
	   struct { int trn, lrg, red; } str;
           int64_t steps; } unhd;
  struct { int count, max; int64_t sum; } part;
  struct {
    int count, skipped, elmd, forced, large, sub, str, blkd, rounds, htes;
    struct { int elm, tried, failed; } small;
    int64_t resolutions, copies, subchks, strchks, steps; } elm;
  struct {
    struct { struct { int irr, red; } dyn; int stat; } sub, str;
    int driving; } otfs;
  struct {
    double prb,dcp,elm,trd,gc,gcd,gcl,gce,gcb,gcu;
    double dst,dfg,red,blk,trj,hte,ana,reb,unhd,part,rsts,lft; } tms;
  struct { int64_t nonmin, learned; } lits;
  struct {
    int64_t learned,glue,nonmaxglue,maxglue,scglue,capped,keptmaxglue;
  } clauses;
  struct {
    int clauses;
    int64_t added, reduced, resolved, forcing, conflicts, saved;
  } lir[MAXGLUE+1];
  const char * prefix;
  FILE * file;
} Stats;

typedef struct Limits {
  int reduce, hla;
  int64_t randec, rephrase;
  struct { int64_t confs; int wasmaxdelta, maxdelta, luby; } restart, rebias;
  struct { int cinc, vinc, irr; int64_t confs, visits, prgss; } dcp;
  struct { int cinc, vinc; int64_t confs, visits; } part;
  struct { int cinc, vinc, irr, pen; int64_t confs, visits, prgss; } dst;
  struct { int cinc, vinc, irr, pen;
           int64_t confs, visits, steps, prgss; } trd, unhd;
  struct { int cinc, vinc, excess, irr, pen;
           int64_t confs, visits, steps, prgss; } elm;
  struct { int cinc, vinc, fixedoreq, irr; int64_t confs, visits; } gc;
  struct { int cinc, vinc, irr, pen; int64_t confs, visits, prgss; } prb, lft;
  struct { int64_t pshwchs, prgss; } dfg;
  struct { int pen; int64_t steps; } hte;
  struct { int64_t steps; } term, sync;
} Limits;

typedef struct Stk { int * start, * top, * end; } Stk;

typedef int Exp;
typedef uint64_t Mnt;
typedef int64_t Flt;
typedef int64_t Scr;
typedef signed char Val;

typedef struct HTS { int offset, count; }  HTS;
typedef struct DVar { HTS hts[2]; } DVar;

typedef struct Ext {
  unsigned equiv:1, melted:1, blocking:2, eliminated:1, tmpfrozen:1;
  int val:2, repr, frozen, etrailpos;
} Ext;

typedef struct TD { int level, dom; int rsn[2]; } TD;

typedef struct AVar {
  Scr score; int part, pos;
  Tag type : 4;
#ifndef NDEBUG
  unsigned simp : 1, wasfalse : 1;
#endif
  int phase : 2, bias : 2;
  unsigned poisoned : 1;
  int mark, trail;
} AVar;

typedef struct EVar { int occ[2], score, pos; } EVar;

typedef struct Conf { int lit, rsn[2]; } Conf;

typedef struct Lir { Stk lits; } Lir;

typedef struct DFPR { int discovered, finished, parent, root; } DFPR;
typedef struct DFOPF { int observed, pushed, flag; } DFOPF;

typedef enum Wrag {
  PREFIX = 0,
  BEFORE = 1,
  AFTER = 2,
  POSTFIX = 3,
} Wrag;

typedef struct Work {
  Wrag wrag : 2;
  int lit : 30;
  int other : 30;
  unsigned red : 1;
  unsigned removed : 1;
} Work;

typedef struct Wtk { Work * start, * top, * end; } Wtk;

typedef struct Ctr { int decision : 31; unsigned used : 1; } Ctr;

typedef struct Ctk { Ctr * start, * top, * end; } Ctk;

typedef struct DF { int discovered, finished; } DF;

typedef struct Part { int vars, clauses, orig, sat; } Part;

typedef struct DFL {
  int discovered, finished;
  union { int lit, sign; };
#ifndef NLGLOG
  int lit4logging;
#endif
} DFL;

typedef struct ASL { int act, size, lidx; } ASL;

typedef enum State {
  UNUSED 	= (1<<0),
  OPTSET 	= (1<<1),
  USED 		= (1<<2),
  READY		= (1<<3),
  UNKNOWN	= (1<<4),
  SATISFIED	= (1<<5),
  EXTENDED      = (1<<6),
  UNSATISFIED	= (1<<7),
  RESET		= (1<<8),
} State;

typedef struct RNG { unsigned z, w; } RNG;

#if !defined(NDEBUG) || !defined(NLGLOG)
#define RESOLVENT
#endif

struct LGL {
  State state;
  Opts opts;
  Ext * ext; int maxext; size_t szext;
  DVar * dvars; AVar * avars; Val * vals;  EVar * evars;
  int nvars, szvars, * i2e, * repr;
  Flt scinc, scincf, maxscore;
  Stk clause, dsched, esched, extend, sortstk, resolvent;
  Stk irr; int mt; Lir red[MAXGLUE+1];
  struct { struct { Stk bin, trn; } red, irr; } dis;
  struct { int pivot, negcls, necls, neglidx;
    Stk lits, next, csigs, lsigs, sizes, occs, noccs, mark, m2i; } elm;
  Stk trail, etrail, frames, saved, clv; TD * drail; int szdrail;
  Stk wchs; int freewchs[MAXLDFW], nfreewchs;
  Ctk control;
  int next, flushed, level, decision, unassigned, assume, eassume, failed;
  struct { struct { DF * dfs; int ndfs, szdfs; } pos, neg; } df;
  Conf conf; Stk seen, poisoned;
  unsigned flips;
  RNG rng;
  char decomposing, measureagility, probing, distilling, lifting;
  char simp, eliminating, simplifying, blocking, unhiding, frozen;
  char dense, propred, igntrn, partitioned;
  int activepart;
  int ignlidx, ignlits[3];
  int tid, tids;
  int bias;
  Limits limits;
  Stats stats;
  struct { int (*fun)(void*); void * state; int done; } term;
  struct {
    struct { void (*fun)(void*,int); void * state; } produce, consumed;
    struct { void(*fun)(void*,int**,int**); void*state; } consume;
  } units;
  struct {
    struct { int * (*fun)(void*); void * state; } lock;
    struct { void (*fun)(void*,int,int); void * state; } unlock;
  } eqs;
  struct { void(*lock)(void*); void (*unlock)(void*); void*state; } msglock;
  double (*getime)(void);
  FILE * apitrace; int closeapitrace;
  void (*onabort)(void *);
  void * abortstate;
#ifndef NCHKSOL
  Stk orig;
#endif
#if !defined(NLGLOG) || !defined(NDEBUG)
  int currentfltstr;
  char fltstr[MAXFLTSTR][100];
#endif
#ifndef NLGLPICOSAT
  struct { int res, chk, init; } picosat;
#endif
};

typedef int64_t Cnf;
typedef uint64_t Fun[FUNQUADS];

#define LT(n) n, n, n, n, n, n, n, n, n, n, n, n, n, n, n, n

static const char lglfloorldtab[256] =
{
// 0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15
  -1, 0, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3,
  LT(4), LT(5), LT(5), LT(6), LT(6), LT(6), LT(6),
  LT(7), LT(7), LT(7), LT(7), LT(7), LT(7), LT(7), LT(7)
};

static const uint64_t lglbasevar2funtab[6] = {
  0xaaaaaaaaaaaaaaaaull, 0xccccccccccccccccull, 0xf0f0f0f0f0f0f0f0ull,
  0xff00ff00ff00ff00ull, 0xffff0000ffff0000ull, 0xffffffff00000000ull,
};

static int lglfloorld (int n) {
  assert (n >= 0);
  if (n < (1<<8)) return lglfloorldtab[n];
  if (n < (1<<16)) return 8 + lglfloorldtab[n>>8];
  if (n < (1<<24)) return 16 + lglfloorldtab[n>>16];
  return 24 + lglfloorldtab[n>>24];
}

static int lglispow2 (int n) {
  assert (0 <= n && n <= INT_MAX);
  return !(n & (n - 1));
}

static int lglceilld (int n) {
  int res = lglfloorld (n);
  if (!lglispow2 (n)) res++;
  return res;
}

static int lglceilsqrt32 (int x) {
  int l, m, r, ll, mm, rr;
  l = 0; ll = l*l;
  if (x <= 0) return 0;
  r = 46340; rr = r*r;
  if (x >= rr) return r;
  for (;;) {
    assert (l < r);
    assert (ll < x && x < rr);
    if (r - l == 1) return r;
    m = (l + r)/2;
    mm = m*m;
    if (mm == x) return m;
    if (mm < x) l = m, ll = mm;
    else r = m, rr = mm;
  }
}

static int lglceilsqrt64 (int x) {
  int64_t l, m, r, ll, mm, rr;
  l = 0; ll = l*l;
  if (x <= 0) return 0;
  r = 3037000499ll; rr = r*r;
  if (x >= rr) return r;
  for (;;) {
    assert (l < r);
    assert (ll < x && x < rr);
    if (r - l == 1) return r;
    m = (l + r)/2;
    mm = m*m;
    if (mm == x) return m;
    if (mm < x) l = m, ll = mm;
    else r = m, rr = mm;
  }
}

static void lglchkflt (Flt a) {
#ifndef NDEBUG
  assert (a >= 0);
  assert (FLTMAX >= (uint64_t) a);
#else
  (void) a;
#endif
}

static Exp lglexp (Flt a) {
  Exp res = a >> FLTPRC;
  assert (0 <= res && res <= EXPMAX);
  res -= EXPZRO;
  return res;
}

static Mnt lglmnt (Flt a) {
  Mnt res = a & MNTMAX;
  res |= MNTBIT;
  assert (res <= MNTMAX);
  return res;
}

static Flt lglflt (Exp e, Mnt m) {
  Flt res;
  if (!m) return FLTMIN;
  if (m < MNTBIT) {
    while (!(m & MNTBIT)) {
      m <<= 1;
      if (e > INT_MIN) e--;
      else break;
    }
  } else  {
    while (m > MNTMAX) {
       m >>= 1;
       if (e > INT_MIN) e++;
       else break;
    }
  }
  if (e < -EXPZRO) return FLTMIN;
  if (e > EXPMAX - EXPZRO) return FLTMAX;
  e += EXPZRO;
  assert (0 <= e && e <= EXPMAX);
  assert (m <= MNTMAX);
  assert (m & MNTBIT);
  res = m & ~MNTBIT;
  res |= ((Flt)e) << FLTPRC;
  return res;
}

static Flt lglrat (unsigned n, unsigned d) {
  Mnt m;
  Exp e;
  if (!n) return FLTMIN;
  if (!d) return FLTMAX;
  m = n;
  e = 0;
  while (!(m & (1ull << 63))) m <<= 1, e--;
  m /= d;
  return lglflt (e, m);
}

#ifndef NLGLOG
double lglflt2dbl (Flt a) {
  return lglmnt (a) * pow (2.0, lglexp (a));
}
#endif

#if !defined(NLGLOG) && !defined(NDEBUG)
static const char * lglflt2str (LGL * lgl, Flt a) {
  double d, e;
  if (a == FLTMIN) return "0";
  if (a == FLTMAX) return "inf";
  d = lglmnt (a);
  d /= 4294967296ll;
  e = lglexp (a);
  e += 32;
  lgl->currentfltstr++;
  if (lgl->currentfltstr == MAXFLTSTR) lgl->currentfltstr = 0;
  sprintf (lgl->fltstr[lgl->currentfltstr], "%.6fd%+03.0f", d, e);
  return lgl->fltstr[lgl->currentfltstr];
}
#endif

static Flt lgladdflt (Flt a, Flt b) {
  Exp e, f, g;
  Mnt m, n, o;
  lglchkflt (a);
  lglchkflt (b);
  if (a == FLTMAX) return FLTMAX;
  if (b == FLTMAX) return FLTMAX;
  if (a == FLTMIN) return b;
  if (b == FLTMIN) return a;
  e = lglexp (a);
  f = lglexp (b);
  if (e < f) g = e, e = f, f = g, o = a, a = b, b = o;
  m = lglmnt (a);
  n = lglmnt (b);
  m += n >> (e - f);
  return lglflt (e, m);
}

static Flt lglmulflt (Flt a, Flt b) {
  Exp e, ea, eb;
  Mnt m, ma, mb;
  lglchkflt (a);
  lglchkflt (b);
  if (a == FLTMAX) return FLTMAX;
  if (b == FLTMAX) return FLTMAX;
  if (a == FLTMIN) return FLTMIN;
  if (b == FLTMIN) return FLTMIN;
  ea = lglexp (a); eb = lglexp (b);
  if (ea > 0 && eb > 0 && (INT_MAX - ea < eb)) return FLTMAX;
  e = ea + eb;
  if (e > EXPMAX - EXPZRO - 32) return FLTMAX;
  e += 32;
  ma = lglmnt (a); mb = lglmnt (b);
  ma >>= 1; mb >>= 1;
  m = ma * mb;
  assert (3ull << 62);
  m >>= 30;
  return lglflt (e, m);
}

static Flt lglshflt (Flt a, int s) {
  Exp e;
  Mnt m;
  if (a == FLTMAX) return FLTMAX;
  if (a == FLTMIN) return FLTMIN;
  assert (0 <= s);
  e = lglexp (a);
  if (e < INT_MIN + s) return FLTMIN;
  e -= s;
  m = lglmnt (a);
  return lglflt (e, m);
}

static int lglfltcmp (Flt a, Flt b) {
  if (a < b) return -1;
  if (a > b) return 1;
  return 0;
}

static void lglwrn (const char * msg, ...) {
  va_list ap;
  printf ("*** warning in '%s': ", __FILE__);
  va_start (ap, msg);
  vprintf (msg, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

static void lgldie (const char * msg, ...) {
  va_list ap;
  printf ("*** internal error in '%s': ", __FILE__);
  va_start (ap, msg);
  vprintf (msg, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
  exit (0);
}

static void lglabort (LGL * lgl) {
  if (lgl->onabort) lgl->onabort (lgl->abortstate);
  if (lgl->opts.exitonabort.val) exit (1);
  abort ();
}

static void lglmsgstart (LGL * lgl, int level) {
  assert (lgl->opts.verbose.val >= level);
  if (lgl->msglock.lock) lgl->msglock.lock (lgl->msglock.state);
  fputc ('c', stdout);
  if (lgl->tid >= 0) printf (" %d", lgl->tid);
  fputc (' ', stdout);
}

static void lglmsgend (LGL * lgl) {
  fputc ('\n', stdout);
  fflush (stdout);
  if (lgl->msglock.unlock) lgl->msglock.unlock (lgl->msglock.state);
}

static void lglprt (LGL * lgl, int level, const char * msg, ...) {
  va_list ap;
  if (lgl->opts.verbose.val < level) return;
  lglmsgstart (lgl, level);
  va_start (ap, msg);
  vprintf (msg, ap);
  va_end (ap);
  lglmsgend (lgl);
}

#ifndef NLGLOG
static void lglogstart (LGL * lgl, int level, const char * msg, ...) {
  va_list ap;
  assert (lgl->opts.log.val >= level);
  if (lgl->msglock.lock) lgl->msglock.lock (lgl->msglock.state);
  fputs ("c ", stdout);
  if (lgl->tid >= 0) printf ("%d ", lgl->tid);
  printf ("LOG%d %d ", level, lgl->level);
  va_start (ap, msg);
  vprintf (msg, ap);
  va_end (ap);
}

#define lglogend lglmsgend
#endif

void lglsetid (LGL * lgl, int tid, int tids) {
  ABORTIF (!lgl, "uninitialized manager");
  assert (lgl->tid < 0 && lgl->tids < 0);
  assert (0 <= tid && tid < tids);
  lgl->tid = tid;
  lgl->tids = tids;
}

void lglseterm (LGL * lgl, int (*fun)(void*), void * state) {
  ABORTIF (!lgl, "uninitialized manager");
  lgl->term.fun = fun;
  lgl->term.state = state;
}

void lglsetproduceunit (LGL * lgl, void (*fun) (void*, int), void * state) {
  ABORTIF (!lgl, "uninitialized manager");
  lgl->units.produce.fun = fun;
  lgl->units.produce.state = state;
}

void lglsetconsumeunits (LGL * lgl,
                         void (*fun) (void*, int **, int **),
		         void * state) {
  ABORTIF (!lgl, "uninitialized manager");
  lgl->units.consume.fun =  fun;
  lgl->units.consume.state = state;
}

void lglsetlockeq (LGL * lgl, int * (*fun)(void*), void * state) {
  ABORTIF (!lgl, "uninitialized manager");
  lgl->eqs.lock.fun = fun;
  lgl->eqs.lock.state = state;
}

void lglsetunlockeq (LGL * lgl, void (*fun)(void*,int,int), void * state) {
  ABORTIF (!lgl, "uninitialized manager");
  lgl->eqs.unlock.fun = fun;
  lgl->eqs.unlock.state = state;
}

void lglsetconsumedunits (LGL * lgl,
                          void (*fun) (void*, int), void * state) {
  ABORTIF (!lgl, "uninitialized manager");
  lgl->units.consumed.fun = fun;
  lgl->units.consumed.state = state;
}

void lglsetmsglock (LGL * lgl,
		    void (*lock)(void*), void (*unlock)(void*),
		    void * state) {
  ABORTIF (!lgl, "uninitialized manager");
  lgl->msglock.lock = lock;
  lgl->msglock.unlock = unlock;
  lgl->msglock.state = state;
}

void lglsetime (LGL * lgl, double (*time)(void)) { lgl->getime = time; }

static void lglinc (LGL * lgl, size_t bytes) {
  lgl->stats.bytes.current += bytes;
  if (lgl->stats.bytes.max < lgl->stats.bytes.current) {
    lgl->stats.bytes.max = lgl->stats.bytes.current;
    LOG (5, "maximum allocated %ld bytes", lgl->stats.bytes.max);
  }
}

static void lgldec (LGL * lgl, size_t bytes) {
  assert (lgl->stats.bytes.current >= bytes);
  lgl->stats.bytes.current -= bytes;
}

static void * lglmalloc (LGL * lgl, size_t bytes) {
  void * res;
  if (!bytes) return 0;
  res = malloc (bytes);
  if (!res) lgldie ("out of memory allocating %ld bytes", bytes);
  LOG (5, "allocating %p with %ld bytes", res, bytes);
  lglinc (lgl, bytes);
  memset (res, 0, bytes);
  return res;
}

static void lglfree (LGL * lgl, void * ptr, size_t bytes) {
  if (!ptr) { assert (!bytes); return; }
  lgldec (lgl, bytes);
  LOG (5, "freeing %p with %ld bytes", ptr, bytes);
  free (ptr);
}

static void * lglrealloc (LGL * lgl, void * ptr, size_t old, size_t new) {
  void * res;
  assert (!ptr == !old);
  if (!ptr) return lglmalloc (lgl, new);
  if (!new) { lglfree (lgl, ptr, old); return 0; }
  lgldec (lgl, old);
  res = realloc (ptr, new);
  if (!res) lgldie ("out of memory reallocating %ld to %ld bytes", old, new);
  LOG (5, "reallocating %p to %p from %ld to %ld bytes", ptr, res, old, new);
  lglinc (lgl, new);
  if (new > old) memset (res + old, 0, new - old);
  return res;
}

static int lglfullstk (Stk * s) { return s->top == s->end; }
static int lglmtstk (Stk * s) { return s->top == s->start; }
static size_t lglcntstk (Stk * s) { return s->top - s->start; }
static size_t lglszstk (Stk * s) { return s->end - s->start; }

static int lglpeek (Stk * s, int pos) {
  assert (0 <= pos && pos < lglszstk (s));
  return s->start[pos];
}

static void lglpoke (Stk * s, int pos, int val) {
  assert (0 <= pos && pos <= lglszstk (s));
  s->start[pos] = val;
}

static void lglenlstk (LGL * lgl, Stk * s) {
  size_t old_size = lglszstk (s);
  size_t new_size = old_size ? 2 * old_size : 1;
  size_t count = lglcntstk (s);
  RSZ (s->start, old_size, new_size);
  s->top = s->start + count;
  s->end = s->start + new_size;
}

static void lglrelstk (LGL * lgl, Stk * s) {
  DEL (s->start, lglszstk (s));
  s->start = s->top = s->end = 0;
}

static void lglshrstk (LGL * lgl, Stk * s, int new_size) {
  size_t old_size, count = lglcntstk (s);
  assert (new_size >= 0);
  assert (count <= new_size);
  if (new_size > 0) {
    old_size = lglszstk (s);
    RSZ (s->start, old_size, new_size);
    s->top = s->start + count;
    s->end = s->start + new_size;
  } else lglrelstk (lgl, s);
}

static void lglfitstk (LGL * lgl, Stk * s) {
  lglshrstk (lgl, s, lglcntstk (s));
}

static void lglpushstk (LGL * lgl, Stk * s, int elem) {
  if (lglfullstk (s)) lglenlstk (lgl, s);
  *s->top++ = elem;
}

#if !defined(NDEBUG) || !defined(NLGLOG)
static void lglrmstk (Stk * s, int elem) {
  int * p, * q;
  for (p = s->start; p < s->top; p++)
    if (*p == elem) break;
  assert (p < s->top);
  q = p++;
  while (p < s->top)
    *q++ = *p++;
  s->top = q;
}
#endif

static int lglpopstk (Stk * s) { assert (!lglmtstk (s)); return *--s->top; }

static int lgltopstk (Stk * s) { assert (!lglmtstk (s)); return s->top[-1]; }

static void lglrststk (Stk * s, int newsz) {
  assert (0 <= newsz && newsz <= lglcntstk (s));
  s->top = s->start + newsz;
}

static void lglredstk (LGL * lgl, Stk * s, int minsize, int pow2smaller) {
  size_t oldsize, count, limit, newsize;
  assert (pow2smaller >= 2);
  oldsize = lglszstk (s);
  if (oldsize <= minsize) return;
  count = lglcntstk (s);
  limit = oldsize >> pow2smaller;
  if (count > limit) return;
  newsize = oldsize / 2;
  if (newsize > 0) {
    RSZ (s->start, oldsize, newsize);
    s->top = s->start + count;
    s->end = s->start + newsize;
  } else lglrelstk (lgl, s);
}

static void lglclnstk (Stk * s) { lglrststk (s, 0); }

static void lgltrapi (LGL * lgl, const char * msg, ...) {
  va_list ap;
  assert (lgl->apitrace);
  va_start (ap, msg);
  vfprintf (lgl->apitrace, msg, ap);
  va_end (ap);
  fputc ('\n', lgl->apitrace);
}

#define TRAPI(MSG,ARGS...) \
do { \
  if (!lgl->apitrace) break; \
  lgltrapi (lgl, MSG, ##ARGS); \
} while (0)

static void lglopenapitrace (LGL * lgl, const char * name) {
  FILE * file;
  char * cmd;
  int len;
  len = strlen (name);
  if (len >= 3 && !strcmp (name + len - 3, ".gz")) {
    len += 20;
    NEW (cmd, len);
    sprintf (cmd, "gzip -c > %s", name);
    file = popen (cmd, "w");
    DEL (cmd, len);
    if (file) lgl->closeapitrace = 2;
  } else {
    file = fopen (name, "w");
    if (file) lgl->closeapitrace = 1;
  }
  if (file) lgl->apitrace = file;
  else lglwrn ("can not write '%s", name);
  TRAPI ("init");
}

#if !defined(NLGLPICOSAT) && !defined(NDEBUG)

static void lglpicosatinit (LGL * lgl) {
  if (lgl->tid >= 0) return;
  if (lgl->picosat.init) return;
  picosat_init ();
  picosat_set_prefix ("c PST ");
  lgl->picosat.chk = 1;
  picosat_add (1);
  picosat_add (0);
  lgl->picosat.init = 1;
  LOG (1, "PicoSAT initialized");
}

#endif

static void lglgetenv (LGL * lgl, Opt * opt, const char * lname) {
  const char * q, * valstr;
  char uname[40], * p;
  int newval, oldval;
  assert (strlen (lname) + 3 + 1 < sizeof (uname));
  uname[0] = 'L';
  uname[1] = 'G';
  uname[2] = 'L';
  p = uname + 3;
  for (q = lname; *q; q++) {
    assert (p < uname + sizeof uname);
    *p++ = toupper (*q);
  }
  assert (p < uname + sizeof uname);
  *p = 0;
  valstr = getenv (uname);
  if (!valstr) return;
  oldval = opt->val;
  newval = atoi (valstr);
  if (newval < opt->min) newval = opt->min;
  if (newval > opt->max) newval = opt->max;
  if (newval == oldval) return;
  opt->val = newval;
  TRAPI ("option %s %d", lname, newval);
}

static unsigned lglrand (LGL * lgl) {
  unsigned res;
  lgl->rng.z = 36969 * (lgl->rng.z & 65535) + (lgl->rng.z >> 16);
  lgl->rng.w = 18000 * (lgl->rng.w & 65535) + (lgl->rng.w >> 16);
  res = (lgl->rng.z << 16) + lgl->rng.w;
  LOG (5, "rng %u", res);
  return res;
}

static int lglfullctk (Ctk * ctk) { return ctk->top == ctk->end; }

static int lglsizectk (Ctk * ctk) { return ctk->end - ctk->start; }

static int lglcntctk (Ctk * ctk) { return ctk->top - ctk->start; }

static void lglrelctk (LGL * lgl, Ctk * ctk) {
  DEL (ctk->start, lglsizectk (ctk));
  memset (ctk, 0, sizeof *ctk);
}

static void lglenlctk (LGL * lgl, Ctk * ctk) {
  int oldsize = lglsizectk (ctk);
  int newsize = oldsize ? 2*oldsize : 1;
  int count = lglcntctk (ctk);
  RSZ (ctk->start, oldsize, newsize);
  ctk->top = ctk->start + count;
  ctk->end = ctk->start + newsize;
}

static void lglpushcontrol (LGL * lgl, int decision) {
  Ctk * ctk = &lgl->control;
  Ctr * ctr;
  if (lglfullctk (ctk)) lglenlctk (lgl, ctk);
  ctr = ctk->top++;
  ctr->decision = decision;
  ctr->used = 0;
}

static void lglrstcontrol (LGL * lgl, int count) {
  Ctk * ctk = &lgl->control;
  ctk->top = ctk->start + count;
}

static int lglevelused (LGL * lgl, int level) {
  Ctk * ctk = &lgl->control;
  Ctr * ctr;
  assert (0 < level && level < lglcntctk (ctk));
  ctr = ctk->start + level;
  return ctr->used;
}

static void lgluselevel (LGL * lgl, int level) {
  Ctk * ctk = &lgl->control;
  Ctr * ctr;
  assert (0 < level && level < lglcntctk (ctk));
  ctr = ctk->start + level;
  assert (!ctr->used);
  ctr->used = 1;
}

static void lglunuselevel (LGL * lgl, int level) {
  Ctk * ctk = &lgl->control;
  Ctr * ctr;
  assert (0 < level && level < lglcntctk (ctk));
  ctr = ctk->start + level;
  assert (ctr->used);
  ctr->used = 0;
}

#define OPT(SHRT,LNG,VAL,MIN,MAX,DESCRP) \
do { \
  Opt * opt = &lgl->opts.LNG; \
  opt->shrt = SHRT; \
  opt->lng = #LNG; \
  opt->val = VAL; \
  assert (MIN <= VAL); \
  opt->min = MIN; \
  assert (VAL <= MAX); \
  opt->max = MAX; \
  opt->descrp = DESCRP; \
  lglgetenv (lgl, opt, #LNG); \
} while (0)

LGL * lglinit (void) {
  const int K = 1000, M = K*K, I = INT_MAX;
  const char * apitracename;
  LGL * lgl;
  int i;

  assert (sizeof (long) == sizeof (void*));

  //assert (INT_MAX > REMOVED);
  assert (REMOVED > ((MAXVAR << RMSHFT) | MASKCS | REDCS));
  assert (REMOVED > MAXREDLIDX);
  assert (REMOVED > MAXIRRLIDX);

  assert (INT_MAX > ((MAXREDLIDX << GLUESHFT) | GLUEMASK));
  assert (INT_MAX > ((MAXIRRLIDX << RMSHFT) | MASKCS | REDCS));

  assert (MAXGLUE < POW2GLUE);

  lgl = malloc (sizeof *lgl);
  CLRPTR (lgl);

  lgl->tid = lgl->tids = -1;

  for (i = 0; i < MAXLDFW; i++) lgl->freewchs[i] = INT_MAX;

  lglpushcontrol (lgl, 0);
  assert (lglcntctk (&lgl->control) == lgl->level + 1);

  lglpushstk (lgl, &lgl->wchs, INT_MAX);
  lglpushstk (lgl, &lgl->wchs, INT_MAX);

  lgl->measureagility = 1;
  lgl->propred = 1;
  lgl->ignlidx = -1;

  apitracename = getenv ("LGLAPITRACE");
  if (apitracename) lglopenapitrace (lgl, apitracename);

  OPT(0,acts,2,0,2,"activity based reduction: 0=disable,1=enable,2=dyn");
  OPT(0,actavgmax,120,0,200,"glue average max limit for dyn acts");
  OPT(0,actstdmin,20,0,200,"glue standard deviation min limit for dyn acts");
  OPT(0,actstdmax,80,0,200,"glue standard deviation max limit for dyn acts");
  OPT(0,agile,23,0,100,"agility limit for restarts");
  OPT(0,bias,2,-1,2,"decision order initial bias (0=nobias,2=cutwidth)");
  OPT(0,block,1,0,1,"enable initial blocked clause elimination");
  OPT(0,blkclslim,2000,3,I,"max blocked clause size");
  OPT(0,blkmaxeff,80*M,0,I,"max effort in blocked clause elimination");
  OPT(0,blkmineff,3*M,0,I,"min effort in blocked clause elimination");
  OPT(0,blkreleff,30,0,K,"rel effort in blocked clause elimination");
  OPT(0,blkocclim,2000,3,I,"max occurrences in blocked clause elimination");
  OPT(0,caplen,10000,1,I,"cap long learned clauses in percent of average");
#ifndef NDEBUG
  OPT('c',check,0,0,2,"check level");
#endif
  OPT(0,deactivate,0,0,1,"deactivate partitions");
  OPT(0,decompose,1,0,1,"enable decompose");
  OPT(0,dcpirrintinc,20*K,10,M,"decompose irredundant interval increment");
  OPT(0,dcpcintinc,20*K,10,100*K,"decompose conflicts interval increment");
  OPT(0,dcpvintinc,20*M,10,200*M,"decompose visits interval increment");
  OPT(0,distill,1,0,1,"enable distillation");
  OPT(0,dstirrintinc,30*K,10,M,"distill irredundant interval increment");
  OPT(0,dstcintinc,40*K,10,100*K,"distill conflict interval increment");
  OPT(0,dstvintinc,40*M,10,200*M,"distill visits interval increment");
  OPT(0,dstmaxeff,60*M,0,I,"max effort in distilling");
  OPT(0,dstmineff,600*K,0,I,"min effort in distilling");
  OPT(0,dstreleff,15,0,K,"rel effort in distilling");
  OPT(0,defragfree,50,10,K,"defragmentation free watches limit");
  OPT(0,defragint,M,100,I,"defragmentation pushed watches interval");
  OPT(0,elim,1,0,1,"enable eliminiation");
  OPT(0,elmirrintinc,40*K,10,M,"eliminiation irredundant interval inc");
  OPT(0,elmcintinc,30*K,10,M,"eliminiation conflicts interval increment");
  OPT(0,elmvintinc,30*M,1,200*M,"eliminiation visits interval increment");
  OPT(0,elmhte,1,0,1,"enabled hte during elimination");
  OPT(0,elmhtelim,2000,0,I,"hte during elimination resolvent limit");
  OPT(0,elmclslim,1000,3,I,"max antecendent size in elimination");
  OPT(0,elmaxeff,600*M,0,I,"max effort in eliminiation");
  OPT(0,elmineff,15*M,0,I,"min effort in eliminiation");
  OPT(0,elmreleff,200,0,10*K,"rel effort in elimination");
  OPT(0,elmocclim,1000,3,I,"max occurences in elimination");
  OPT(0,elmnostr,0,0,I,"number of elimination rounds before strengthening");
  OPT(0,elmreslim,2000,2,I,"max resolvent size in elimination");
  OPT(0,exitonabort,0,0,1,"exit instead abort after internal error");
  OPT(0,gcirrintinc,10*K,10,M, "gc irredundant interval increment");
  OPT(0,gccintinc,10*K,10,M, "gc conflicts interval increment");
  OPT(0,gcvintinc,10*M,10,100*M, "gc visits interval increment");
  OPT(0,gluescale,2,1,3,"glue scaling: 1=linear,2=sqrt,3=ld");
  OPT(0,hlaliminc,5,1,I/4,"hidden literal addition limit increment");
  OPT(0,hlaminlim,5,1,I/2,"hidden literal addition min limit");
  OPT(0,hlamaxlim,10000,1,I/2,"hidden literal addition max limit");
  OPT(0,hte,1,0,1,"enable hte & hlr removal");
  OPT(0,htered,1,0,1,"enable hte & hlr in redundant/learned clauses");
  OPT(0,htemaxeff,100*M,0,I,"max effort in hidden tautology elimination");
  OPT(0,htemineff,M,0,I,"min effort in hidden tautology elimination");
  OPT(0,htereleff,40,0,10*K,"rel effort in hidden tautology elimination");
  OPT(0,keepmaxglue,64,0,I, "keep maxglue (0=never,1=always,2=every2nd,...)");
  OPT(0,lhbr,1,0,1, "enable lazy hyber binary reasoning");
  OPT(0,lift,1,0,1,"enable double lookahead lifting");
  OPT(0,lftirrintinc,10*K,10,M,"lifting irredundant interval increment");
  OPT(0,lftcintinc,20*K,10,100*K,"lifting conflicts interval increment");
  OPT(0,lftvintinc,20*M,1,100*M,"lifting visits interval increment");
  OPT(0,lftmaxeff,40*M,0,I,"max effort in lifting");
  OPT(0,lftmineff,400*K,0,I,"min effort in lifting");
  OPT(0,lftreleff,20,0,10*K,"rel effort in lifting");
#ifndef NLGLOG
  OPT('l',log,0,0,5,"log level");
#endif
  OPT(0,minlim,5,0,I,"minimization budget per literal");
  OPT(0,otfs,1,0,1,"enable on-the-fly subsumption");
  OPT(0,partition,1,0,1,"partition into disconnected components");
  OPT(0,partcintinc,20*K,10,100*K,"partitioning conflicts interval inc");
  OPT(0,partvintinc,20*M,1,100*M,"partitioning visits interval increment");
  OPT(0,phase,0,-1,1,"default phase");
  OPT(0,plain,0,0,1,"plain mode disables all preprocessing");
  OPT(0,probe,1,0,1,"enable probing");
  OPT(0,prbirrintinc,10*K,10,M,"probing irredundant interval increment");
  OPT(0,prbcintinc,20*K,10,100*K,"probing conflicts interval increment");
  OPT(0,prbvintinc,20*M,1,100*M,"probing visits interval increment");
  OPT(0,prbmaxeff,40*M,0,I,"max effort in probing");
  OPT(0,prbmineff,400*K,0,I,"min effort in probing");
  OPT(0,prbreleff,20,0,10*K,"rel effort in probing");
  OPT(0,seed,0,0,I,"random number generator seed");
  OPT(0,smallve,1,0,1,"enable small number variables elimination");
  OPT(0,smallvevars,FUNVAR,4,FUNVAR,
      "variables in small number variables elimination");
  OPT(0,rebias,1,0,1,"enable rebiasing phases");
  OPT(0,rebint,2000,100,I/2,"rebias interval");
  OPT(0,rebflip,5,0,I/2,"rebias flip probability interval");
  OPT(0,rephrase,1,0,1,"reinitialize phase");
  OPT(0,rphrint,20000,0,I,"rephrasing interval");
  OPT(0,rphrfac,100,0,10000,"reprasing interval increment factor");
  OPT(0,randec,1,0,1,"enable random decisions");
  OPT(0,randecint,1000,2,I/2,"random decision interval");
  OPT(0,redlexpinc,70,0,I,"exponential reduce limit increment hits limit");
  OPT(0,redlexpfac,50,0,1000,"exponential reduce limit increment factor");
  OPT(0,redlinit,K,1,100*K,"initial reduce limit");
  OPT(0,redlinc,K,1,10*K,"reduce limit increment");
  OPT(0,redlmininc,10,1,100*K,"rel min reduce limit increment");
  OPT(0,redlmaxinc,200,1,100*K,"rel max reduce limit increment");
  OPT(0,restart,1,0,1,"enable restarting");
  OPT(0,restartint,5,1,I,"restart interval");
  OPT(0,restartype,3,0,3,"restart type: 0=top, 1=match, 2=perm, 3=reuse");
  OPT(0,scincinc,200,0,10*K,"score increment increment in per mille");
  OPT(0,syncint,111111,0,M,"unit synchronization interval");
  OPT(0,termint,122222,0,M,"termination check interval");
  OPT(0,transred,1,0,1,"enable transitive reduction");
  OPT(0,trdirrintinc,10*K,10,M,"transred irredundant interval increment");
  OPT(0,trdcintinc,30*K,1,M,"transred conflicts interval increment");
  OPT(0,trdvintinc,20*M,1,200*M,"transred visits interval increment");
  OPT(0,trdmaxeff,60*M,0,I,"max effort in transitive reduction");
  OPT(0,trdmineff,600*K,0,I,"min effort in transitive reduction");
  OPT(0,trdreleff,6,0,10*K,"rel effort in transitive reduction");
  OPT(0,unhide,1,0,1,"enable unhiding");
  OPT(0,unhdextstamp,1,0,1,"used extended stamping features");
  OPT(0,unhdhbr,0,0,1,"enable unhiding hidden binary resolution");
  OPT(0,unhdirrintinc,10*K,10,M,"unhiding irredundant interval increment");
  OPT(0,unhdcintinc,30*K,1,M,"unhiding conflicts interval increment");
  OPT(0,unhdvintinc,40*M,1,200*M,"unhiding reduction visits interval in");
  OPT(0,unhdmaxeff,100*M,0,I,"max effort in unhiding");
  OPT(0,unhdmineff,1*M,0,I,"min effort in unhiding");
  OPT(0,unhdreleff,30,0,10*K,"rel effort in unhiding");
  OPT(0,unhdlnpr,3,0,I,"unhide no progress round limit");
  OPT(0,unhdroundlim,5,0,100,"unhide round limit");
  OPT('v',verbose,0,0,3,"verbosity level");
  OPT('w',witness,1,0,1,"print witness");

  lgl->scinc = lglflt (0, 1);
  lgl->scincf = lglrat (1000 + lgl->opts.scincinc.val, 1000);
  lgl->maxscore = lglflt (MAXSCOREXP, 1);

  if (abs (lgl->opts.bias.val) <= 1) lgl->bias = lgl->opts.bias.val;
  else lgl->bias = 1;

  lgl->getime = lglprocesstime;

  TRANS (UNUSED);

  return lgl;
}

static int lglmaxoptnamelen (LGL * lgl) {
  int res = 0, len;
  Opt * o;
  for (o = FIRSTOPT (lgl); o <= LASTOPT (lgl); o++)
    if ((len = strlen (o->lng)) > res)
      res = len;
  return res;
}

void lglusage (LGL * lgl) {
  char fmt[20];
  int len;
  Opt * o;
  ABORTIF (!lgl, "uninitialized manager");
  len = lglmaxoptnamelen (lgl);
  sprintf (fmt, "--%%-%ds", len);
  for (o = FIRSTOPT (lgl); o <= LASTOPT (lgl); o++) {
    if (o->shrt) printf ("-%c|", o->shrt); else printf ("   ");
    printf (fmt, o->lng);
    printf (" %s [%d]\n", o->descrp, o->val);
  }
}

void lglopts (LGL * lgl, const char * prefix, int ignsome) {
  Opt * o;
  ABORTIF (!lgl, "uninitialized manager");
  for (o = FIRSTOPT (lgl); o <= LASTOPT (lgl); o++) {
    if (ignsome) {
      if (!strcmp (o->lng, "check")) continue;
      if (!strcmp (o->lng, "log")) continue;
      if (!strcmp (o->lng, "verbose")) continue;
      if (!strcmp (o->lng, "witness")) continue;
    }
    printf ("%s--%s=%d\n", prefix, o->lng, o->val);
  }
}

void lglrgopts (LGL * lgl) {
  Opt * o;
  ABORTIF (!lgl, "uninitialized manager");
  for (o = FIRSTOPT (lgl); o <= LASTOPT (lgl); o++)
    printf ("%s %d %d %d\n", o->lng, o->val, o->min, o->max);
}

int lglhasopt (LGL * lgl, const char * opt) {
  Opt * o;
  ABORTIF (!lgl, "uninitialized manager");
  for (o = FIRSTOPT (lgl); o <= LASTOPT (lgl); o++) {
    if (!opt[1] && o->shrt == opt[0]) return 1;
    if (!strcmp (o->lng, opt)) return 1;
  }
  return 0;
}

void * lglfirstopt (LGL * lgl) { return FIRSTOPT (lgl); }

void * lglnextopt (LGL * lgl,
                   void * current,
		   const char **nameptr,
		   int *valptr, int *minptr, int *maxptr) {
  Opt * opt = current, * res = opt + 1;
  if (res > LASTOPT (lgl)) return 0;
  *nameptr = opt->lng;
  *valptr = opt->val;
  *minptr = opt->min;
  *maxptr = opt->max;
  return res;
}

void lglsetopt (LGL * lgl, const char * opt, int val) {
  Opt * o;
  REQUIRE (UNUSED | OPTSET);
  for (o = FIRSTOPT (lgl); o <= LASTOPT (lgl); o++) {
    if (!opt[1] && o->shrt == opt[0]) break;
    if (!strcmp (o->lng, opt)) break;
  }
  if (o > LASTOPT (lgl)) return;
  if (val < o->min) val = o->min;
  if (o->max < val) val = o->max;
  o->val = val;
  if (lgl->state != OPTSET) TRANS (OPTSET);
  TRAPI ("option %s %d", opt, val);
}

int lglgetopt (LGL * lgl, const char * opt) {
  Opt * o;
  ABORTIF (!lgl, "uninitialized manager");
  for (o = FIRSTOPT (lgl); o <= LASTOPT (lgl); o++) {
    if (!opt[1] && o->shrt == opt[0]) return o->val;
    if (!strcmp (o->lng, opt)) return o->val;
  }
  return 0;
}

void lglwtrapi (LGL * lgl, FILE * apitrace) {
  REQUIRE (UNUSED);
  ABORTIF (lgl->apitrace, "can only write one API trace");
  lgl->apitrace = apitrace;
  TRAPI ("init");
}

void lglonabort (LGL * lgl, void * abortstate, void (*onabort)(void*)) {
  ABORTIF (!lgl, "uninitialized manager");
  lgl->abortstate = abortstate;
  lgl->onabort = onabort;
}

static unsigned lglgcd (unsigned a, unsigned b) {
  unsigned tmp;
  assert (a), assert (b);
  if (a < b) SWAP (a, b);
  while (b) tmp = b, b = a % b, a = tmp;
  return a;
}

static void lglrszvars (LGL * lgl, int new_size) {
  int old_size = lgl->szvars;
  assert (lgl->nvars <= new_size);
  RSZ (lgl->vals, old_size, new_size);
  RSZ (lgl->i2e, old_size, new_size);
  RSZ (lgl->dvars, old_size, new_size);
  RSZ (lgl->avars, old_size, new_size);
  lgl->szvars = new_size;
}

static void lglenlvars (LGL * lgl) {
  size_t old_size, new_size;
  old_size = lgl->szvars;
  new_size = old_size ? 2 * old_size : 4;
  LOG (3, "enlarging internal variables from %ld to %ld", old_size, new_size);
  lglrszvars (lgl, new_size);
}

static void lglredvars (LGL * lgl) {
  size_t old_size, new_size;
  old_size = lgl->szvars;
  new_size = lgl->nvars;
  if (new_size == old_size) return;
  LOG (3, "reducing variables from %ld to %ld", old_size, new_size);
  lglrszvars (lgl, new_size);
}

static int lglmax (int a, int b) { return a > b ? a : b; }

static DVar * lgldvar (LGL * lgl, int lit) {
  assert (2 <= abs (lit) && abs (lit) < lgl->nvars);
  return lgl->dvars + abs (lit);
}

static AVar * lglavar (LGL * lgl, int lit) {
  assert (2 <= abs (lit) && abs (lit) < lgl->nvars);
  return lgl->avars + abs (lit);
}

static int * lgldpos (LGL * lgl, int lit) {
  AVar * av;
  int * res;
  av = lglavar (lgl, lit);
  res = &av->pos;
  return res;
}

static int lgldcmp (LGL * lgl, int l, int k) {
  AVar * av = lglavar (lgl, l);
  AVar * bv = lglavar (lgl, k);
  int res;
  if ((res = (bv->part - av->part))) return res;
  if ((res = lglfltcmp (av->score, bv->score))) return res;
  res = lgl->bias * (l - k);
  return res;
}

#define lglchkact(ACT) \
  do { assert (NOTALIT <= (ACT) && (ACT) < REMOVED - 1); } while (0)

#ifndef NDEBUG
static void lglchkdsched (LGL * lgl) {
  int * p, parent, child, ppos, cpos, size, i, tmp;
  Stk * s = &lgl->dsched;
  size = lglcntstk (s);
  p = s->start;
  for (ppos = 0; ppos < size; ppos++) {
    parent = p[ppos];
    tmp = *lgldpos (lgl, parent);
    assert (ppos == tmp);
    for (i = 0; i <= 1; i++) {
      cpos = 2*ppos + 1 + i;
      if (cpos >= size) continue;
      child = p[cpos];
      tmp = *lgldpos (lgl, child);
      assert (cpos == tmp);
      assert (lgldcmp (lgl, parent, child) >= 0);
    }
  }
}
#endif

static void lgldup (LGL * lgl, int lit) {
  int child = lit, parent, cpos, ppos, * p, * cposptr, * pposptr;
  Stk * s = &lgl->dsched;
  p = s->start;
  cposptr = lgldpos (lgl, child);
  cpos = *cposptr;
  assert (cpos >= 0);
  while (cpos > 0) {
    ppos = (cpos - 1)/2;
    parent = p[ppos];
    if (lgldcmp (lgl, parent, lit) >= 0) break;
    pposptr = lgldpos (lgl, parent);
    assert (*pposptr == ppos);
    p[cpos] = parent;
    *pposptr = cpos;
    LOGDSCHED (5, parent, "down from %d", ppos);
    cpos = ppos;
    child = parent;
  }
  if (*cposptr == cpos) return;
#ifndef NLGLOG
  ppos = *cposptr;
#endif
  *cposptr = cpos;
  p[cpos] = lit;
  LOGDSCHED (5, lit, "up from %d", ppos);
#ifndef NDEBUG
  if (lgl->opts.check.val >= 2) lglchkdsched (lgl);
#endif
}

static void lglddown (LGL * lgl, int lit) {
  int parent = lit, child, right, ppos, cpos;
  int * p, * pposptr, * cposptr, size;
  Stk * s = &lgl->dsched;
  size = lglcntstk (s);
  p = s->start;
  pposptr = lgldpos (lgl, parent);
  ppos = *pposptr;
  assert (0 <= ppos);
  for (;;) {
    cpos = 2*ppos + 1;
    if (cpos >= size) break;
    child = p[cpos];
    if (cpos + 1 < size) {
      right = p[cpos + 1];
      if (lgldcmp (lgl, child, right) < 0) cpos++, child = right;
    }
    if (lgldcmp (lgl, child, lit) <= 0) break;
    cposptr = lgldpos (lgl, child);
    assert (*cposptr = cpos);
    p[ppos] = child;
    *cposptr = ppos;
    LOGDSCHED (5, child, "up from %d", cpos);
    ppos = cpos;
    parent = child;
  }
  if (*pposptr == ppos) return;
#ifndef NLGLOG
  cpos = *pposptr;
#endif
  *pposptr = ppos;
  p[ppos] = lit;
  LOGDSCHED (5, lit, "down from %d", cpos);
#ifndef NDEBUG
  if (lgl->opts.check.val >= 2) lglchkdsched (lgl);
#endif
}

static void lgldsched (LGL * lgl, int lit) {
  int * p = lgldpos (lgl, lit);
  Stk * s = &lgl->dsched;
  assert (*p < 0);
  *p = lglcntstk (s);
  lglpushstk (lgl, s, lit);
  lgldup (lgl, lit);
  lglddown (lgl, lit);
  LOGDSCHED (4, lit, "pushed");
}

static int lgltopdsched (LGL * lgl) {
  assert (!lglmtstk (&lgl->dsched));
  return lgl->dsched.start[0];
}

static int lglpopdsched (LGL * lgl) {
  Stk * s = &lgl->dsched;
  int res, last, cnt, * p;
  AVar * av;
  assert (!lglmtstk (s));
  res = *s->start;
  LOGDSCHED (4, res, "popped");
  av = lglavar (lgl, res);
  assert (!av->pos);
  av->pos = -1;
  last = lglpopstk (s);
  cnt = lglcntstk (s);
  if (!cnt) { assert (last == res); return res; }
  p = lgldpos (lgl, last);
  assert (*p == cnt);
  *p = 0;
  *s->start = last;
  lglddown (lgl, last);
  return res;
}

static Val lglval (LGL * lgl, int lit) {
  int idx = abs (lit);
  Val res;
  assert (2 <= idx && idx < lgl->nvars);
  res = lgl->vals[idx];
  if (lit < 0) res = -res;
  return res;
}

static int lgltrail (LGL * lgl, int lit) { return lglavar (lgl, lit)->trail; }

static TD * lgltd (LGL * lgl, int lit) {
  int pos = lgltrail (lgl, lit);
  assert (0 <= pos && pos < lgl->szdrail);
  return lgl->drail + pos;
}

static int lglevel (LGL * lgl, int lit) { return lgltd (lgl, lit)->level; }

static void lgldreschedule (LGL * lgl) {
  Stk * s = &lgl->dsched;
  int idx, i, pos, cnt = lglcntstk (s);
  AVar * av;
  LOG (1, "rescheduling %d variables", cnt);
  pos = 0;
  s->top = s->start;
  for (i = 0; i < cnt; i++) {
    assert (pos <= i);
    assert (s->start + pos == s->top);
    idx = s->start[i];
    av = lglavar (lgl, idx);
    if (av->type != FREEVAR) { av->pos = -1; continue; }
    assert (av->pos == i);
    s->start[pos] = idx;
    av->pos = pos++;
    s->top++;
    lgldup (lgl, idx);
    lglddown (lgl, idx);
  }
  LOG (1, "new schedule with %d variables", lglcntstk (s));
  lglfitstk (lgl, s);
#ifndef NDEBUG
  if (lgl->opts.check.val >= 1) lglchkdsched (lgl);
#endif
}

static void lglrescorevar (LGL * lgl, int idx) {
  Flt oldscore;
  AVar * av;
  av = lglavar (lgl, idx);
  oldscore = av->score;
  av->score = lglshflt (oldscore, MAXSCOREXP + 1);
  LOG (3, "rescored variable %d from %s to %s",
       idx, lglflt2str (lgl, oldscore), lglflt2str (lgl, av->score));
}

static void lglrescorevars (LGL * lgl) {
  Stk * s = &lgl->dsched;
  int idx, pos, cnt;
  Flt oldscore;
  AVar * av;
  lgl->stats.rescored.vars++;
  cnt = lglcntstk (s);
  for (pos = 0; pos < cnt; pos++) {
    idx = s->start[pos];
    assert (lglavar (lgl, idx)->pos == pos);
    lglrescorevar (lgl, idx);
  }
  for (idx = 2; idx < lgl->nvars; idx++) {
    av = lglavar (lgl, idx);
    if (av->pos >= 0) continue;
    lglrescorevar (lgl, idx);
  }
  lgldreschedule (lgl);
  oldscore = lgl->scinc;
  lgl->scinc = lglshflt (oldscore, MAXSCOREXP + 1);
  if (lgl->scinc < lglflt (SCINCMINEXP, 1))
    lgl->scinc = lglflt (SCINCMINEXP, 1);
  LOG (2, "rescoring new variable score increment from %s to %s",
       lglflt2str (lgl, oldscore), lglflt2str (lgl, lgl->scinc));
}

static int lglbumpscinc (LGL * lgl) {
  Flt oldscinc = lgl->scinc;
  lgl->scinc = lglmulflt (oldscinc, lgl->scincf);
  LOG (3, "bumped variable score increment from %s to %s",
       lglflt2str (lgl, oldscinc), lglflt2str (lgl, lgl->scinc));
  if (lgl->scinc < lgl->maxscore) return 0;
  LOG (2, "variable max score %s hit", lglflt2str (lgl, lgl->maxscore));
  return 1;
}

static int lglnewvar (LGL * lgl) {
  int res;
  AVar * av;
  DVar * dv;
  if (lgl->nvars == lgl->szvars) lglenlvars (lgl);
  if (lgl->nvars) res = lgl->nvars++;
  else res = 2, lgl->nvars = 3;
  assert (res < lgl->szvars);
  if (res > MAXVAR) lgldie ("more than %d variables", MAXVAR - 1);
  assert (((res << RMSHFT) >> RMSHFT) == res);
  assert (((-res << RMSHFT) >> RMSHFT) == -res);
  LOG (3, "new internal variable %d", res);
  dv = lgl->dvars + res;
  CLRPTR (dv);
  av = lgl->avars + res;
  CLRPTR (av);
  av->pos = -1;
  av->score = FLTMIN;
  lgldsched (lgl, res);
  lgl->unassigned++;
  return res;
}

static int lglsgn (int lit) { return (lit < 0) ? -1 : 1; }

static Ext * lglelit2ext (LGL * lgl, int elit) {
  int idx = abs (elit);
  assert (0 < idx && idx <= lgl->maxext);
  return lgl->ext + idx;
}

static int lglerepr (LGL * lgl, int elit) {
  int res, next;
  Ext * ext;
  res = elit;
  for (;;) {
    ext = lglelit2ext (lgl, res);
    if (!ext->equiv) break;
    next = ext->repr;
    if (res < 0) next = -next;
    res = next;
  }
  return res;
}

static void lgladjext (LGL * lgl, int eidx) {
  size_t old, new;
  assert (eidx >= lgl->szext);
  assert (eidx > lgl->maxext);
  assert (lgl->szext >= lgl->maxext);
  old = lgl->szext;
  new = old ? 2*old : 2;
  while (eidx >= new) new *= 2;
  assert (eidx < new && new >= lgl->szext);
  LOG (3, "enlarging external variables from %ld to %ld", old, new);
  RSZ (lgl->ext, old, new);
  lgl->szext = new;
}

static void lglmelter (LGL * lgl) {
  if (!lgl->frozen) return;
  lgl->frozen = 0;
  LOG (2, "melted solver");
}

static int lglimport (LGL * lgl, int elit) {
  int res, repr, eidx = abs (elit);
  Ext * ext;
  assert (elit);
  if (eidx >= lgl->szext) lgladjext (lgl, eidx);
  if (eidx > lgl->maxext) {
    lgl->maxext = eidx;
    lglmelter (lgl);
  }
  repr = lglerepr (lgl, elit);
  ext = lglelit2ext (lgl, repr);
  assert (!ext->equiv);
  res = ext->repr;
  if (!res) {
    res = lglnewvar (lgl);
    assert (!ext->equiv);
    ext->repr = res;
    ext->etrailpos = -1;
    lgl->i2e[res] = eidx;
    LOG (3, "mapping external variable %d to %d", eidx, res);
  }
  if (repr < 0) res = -res;
  LOG (2, "importing %d as %d", elit, res);
  return res;
}

static int * lglidx2lits (LGL * lgl, int red, int lidx) {
  int * res, glue = 0;
  Stk * s;
  assert (red == 0 || red == REDCS);
  assert (0 <= lidx);
  if (red) {
    glue = lidx & GLUEMASK;
    lidx >>= GLUESHFT;
    assert (lidx <= MAXREDLIDX);
    s = &lgl->red[glue].lits;
  } else s = &lgl->irr;
  res = s->start + lidx;
#ifndef NDEBUG
  if (red && glue == MAXGLUE) assert (res < s->end);
  else assert (res < s->top);
#endif
  return res;
}

#ifndef NLGLOG
static const char * lglred2str (int red) {
  assert (!red || red == REDCS);
  return red ? "redundant" : "irredundant";
}
#endif

static int lglisfree (LGL * lgl, int lit) {
  return lglavar (lgl, lit)->type == FREEVAR;
}

static int lgliselim (LGL * lgl, int lit) {
  return lglavar (lgl, lit)->type == ELIMVAR;
}

static int lglexport (LGL * lgl, int ilit) {
  assert (2 <= abs (ilit) && abs (ilit) < lgl->nvars);
  return lgl->i2e[abs (ilit)] * lglsgn (ilit);
}

static int * lglrsn (LGL * lgl, int lit) { return lgltd (lgl, lit)->rsn; }

static int lgldom (LGL * lgl, int lit) {
  int res = lgltd (lgl, lit)->dom;
  if (lglval (lgl, lit) < 0) res = -res;
  return res;
}

static HTS * lglhts (LGL * lgl, int lit) {
  return lgldvar (lgl, lit)->hts + (lit < 0);
}

static int * lglhts2wchs (LGL * lgl, HTS * hts) {
  int * res = lgl->wchs.start + hts->offset;
  assert (res < lgl->wchs.top);
  assert (res + hts->count < lgl->wchs.top);
  assert (res + hts->count < lgl->wchs.top);
  return res;
}

static void lglassign (LGL * lgl, int lit, int r0, int r1) {
  AVar * av = lglavar (lgl, lit);
  int idx, phase, glue, tag;
  TD * td;
  LOGREASON (2, lit, r0, r1, "assign %d through", lit);
  av->trail = lglcntstk (&lgl->trail);
  if (av->trail >= lgl->szdrail) {
    int newszdrail = lgl->szdrail ? 2*lgl->szdrail : 1;
    RSZ (lgl->drail, lgl->szdrail, newszdrail);
    lgl->szdrail = newszdrail;
  }
  td = lgltd (lgl, lit);
  tag = r0 & MASKCS;
  if (tag == BINCS) {
    td->dom = -lgldom (lgl, (r0 >> RMSHFT));
    LOG (3, "literal %d dominated by %d", lit, td->dom);
  } else td->dom = lit;
#ifndef NDEBUG
  {
    int * p, red, other, other2, * c, lidx, found;
    if (tag == BINCS || tag == TRNCS) {
      other = r0 >> RMSHFT;
      assert (lglval (lgl, other) < 0);
      if (tag == TRNCS) {
	other2 = r1;
	assert (lglval (lgl, other2) < 0);
      }
    } else if (tag == LRGCS) {
      red = r0 & REDCS;
      lidx = r1;
      c = lglidx2lits (lgl, red, lidx);
      found = 0;
      for (p = c; (other = *p); p++)
	if (other == lit) found++;
	else assert (lglval (lgl, other) < 0);
      assert (found == 1);
    } else assert (tag == DECISION || tag == UNITCS);
  }
  assert (!lglval (lgl, lit));
  assert (lgl->unassigned > 0);
  assert (!lgliselim (lgl, lit));
#endif
  idx = abs (lit);
  phase = lglsgn (lit);
  lgl->vals[idx] = phase;
  if (lgl->measureagility) {
    lgl->flips -= lgl->flips/10000;
    if (av->phase && av->phase != phase) lgl->flips += 1000;
    av->phase = phase;
  }
#ifndef NDEBUG
  if (phase < 0) av->wasfalse = 1; else av->wasfalse = 0;
#endif
  td->level = lgl->level;
  if (!lgl->level) {
    if (av->type == EQUIVAR) {
      assert (lgl->stats.equiv.current > 0);
      lgl->stats.equiv.current--;
    } else {
      assert (av->type == FREEVAR);
      av->type = FIXEDVAR;
    }
    lgl->stats.fixed.sum++;
    lgl->stats.fixed.current++;
    lgl->stats.prgss++;
    td->rsn[0] = UNITCS | (lit << RMSHFT);
    td->rsn[1] = 0;
    if (lgl->units.produce.fun)  {
      LOG (2, "trying to export internal unit %d external %d\n",
           lgl->tid, lit, lglexport (lgl, lit));
      lgl->units.produce.fun (lgl->units.produce.state, lglexport (lgl, lit));
      LOG (2, "exporting internal unit %d external %d\n",
              lgl->tid, lit, lglexport (lgl, lit));
    }
  } else {
    td->rsn[0] = r0;
    td->rsn[1] = r1;
  }
  lglpushstk (lgl, &lgl->trail, lit);
  lgl->unassigned--;
  if ((r0 & REDCS) && (r0 & MASKCS) == LRGCS) {
    glue = r1 & GLUEMASK;
    lgl->stats.lir[glue].forcing++;
    assert (lgl->stats.lir[glue].forcing > 0);
  }
  __builtin_prefetch (lglhts2wchs (lgl, lglhts (lgl, -lit)));
}

static void lglf2rce (LGL * lgl, int lit, int other, int red) {
  assert (lglval (lgl, other) < 0);
  assert (!red || red == REDCS);
  assert (!lgliselim (lgl, other));
  lglassign (lgl, lit, ((other << RMSHFT) | BINCS | red), 0);
}

static void lglf3rce (LGL * lgl, int lit, int other, int other2, int red) {
  assert (lglval (lgl, other) < 0);
  assert (lglval (lgl, other2) < 0);
  assert (!lgliselim (lgl, other));
  assert (!lgliselim (lgl, other2));
  assert (!red || red == REDCS);
  lglassign (lgl, lit, ((other << RMSHFT) | TRNCS | red), other2);
}

static void lglflrce (LGL * lgl, int lit, int red, int lidx) {
#ifndef NDEBUG
  int * p = lglidx2lits (lgl, red, lidx), other;
  while ((other = *p++)) {
    assert (!lgliselim (lgl, other));
    if (other != lit) assert (lglval (lgl, other) < 0);
  }
  assert (red == 0 || red == REDCS);
#endif
  lglassign (lgl, lit, red | LRGCS, lidx);
}

static void lglunassign (LGL * lgl, int lit) {
  int idx = abs (lit), r0, r1, tag, lidx, glue, * rsn;
  AVar * av = lglavar (lgl, lit);
  LOG (2, "unassign %d", lit);
  assert (lglval (lgl, lit) > 0);
  assert (lgl->vals[idx] == lglsgn (lit));
  lgl->vals[idx] = 0;
  lgl->unassigned++;
  assert (lgl->unassigned > 0);
  if (av->pos < 0) lgldsched (lgl, idx);
  rsn = lglrsn (lgl, lit);
  r0 = rsn[0];
  if (!(r0 & REDCS)) return;
  tag = r0 & MASKCS;
  if (tag != LRGCS) return;
  r1 = rsn[1];
  glue = r1 & GLUEMASK;
  if (glue < MAXGLUE) return;
  lidx = r1 >> GLUESHFT;
  LOG (2, "eagerly deleting maximum glue clause at %d", lidx);
  lglrststk (&lgl->red[glue].lits, lidx);
  lglredstk (lgl, &lgl->red[glue].lits, (1<<20), 3);
}

#ifndef NDEBUG
static Val lglfixed (LGL * lgl, int lit) {
  int res;
  if (!(res = lglval (lgl, lit))) return 0;
  if (lglevel (lgl, lit) > 0) return 0;
  return res;
}
#endif

static void lglbacktrack (LGL * lgl, int level) {
  int lit;
  assert (level >= 0);
  LOG (2, "backtracking to level %d", level);
  assert (level <= lgl->level);
  while (!lglmtstk (&lgl->trail)) {
    lit = lgltopstk (&lgl->trail);
    assert (abs (lit) > 1);
    if (lglevel (lgl, lit) <= level) break;
    lglunassign (lgl, lit);
    lgl->trail.top--;
  }
  lgl->level = level;
  lglrstcontrol (lgl, level + 1);
  assert (lglcntctk (&lgl->control) == lgl->level + 1);
  lgl->conf.lit = 0;
  lgl->conf.rsn[0] = lgl->conf.rsn[1] = 0;
  lgl->next = lglcntstk (&lgl->trail);
  LOG (2, "backtracked ");
}

static int lglmarked (LGL * lgl, int lit) {
  int res = lglavar (lgl, lit)->mark;
  if (lit < 0) res = -res;
  return res;
}

#ifndef NLGLPICOSAT

#ifndef NDEBUG
static void lglpicosataddcls (LGL* lgl, const int * c){
  const int * p;
  if (lgl->tid >= 0 || !lgl->opts.check.val) return;
  lglpicosatinit (lgl);
  for (p = c; *p; p++) picosat_add (*p);
  picosat_add (0);
}
#endif

static void lglpicosatchkclsaux (LGL * lgl, int * c) {
#ifndef NDEBUG
  int * p, other;
  lglpicosatinit (lgl);
  if (lgl->tid >= 0 || !lgl->opts.check.val) return;
  if (picosat_inconsistent ()) {
    LOG (3, "no need to check since PicoSAT is already inconsistent");
    return;
  }
  LOGCLS (3, c, "checking consistency with PicoSAT of clause");
  for (p = c; (other = *p); p++) picosat_assume (-other);
  (void) picosat_sat (-1);
  assert (picosat_res() == 20);
#endif
}

static void lglpicosatchkcls (LGL * lgl) {
  lglpicosatchkclsaux (lgl, lgl->clause.start);
}

static void lglpicosatchkclsarg (LGL * lgl, int first, ...) {
#ifndef NDEBUG
  va_list ap;
  Stk stk;
  int lit;
  if (!lgl->opts.check.val) return;
  lglpicosatinit (lgl);
  CLR (stk);
  if (first) {
    va_start (ap, first);
    lglpushstk (lgl, &stk, first);
    for (;;) {
      lit = va_arg (ap, int);
      if (!lit) break;
      lglpushstk (lgl, &stk, lit);
    }
    va_end (ap);
  }
  lglpushstk (lgl, &stk, 0);
  lglpicosatchkclsaux (lgl, stk.start);
  lglrelstk (lgl, &stk);
#endif
}

static void lglpicosatchkunsat (LGL * lgl) {
#ifndef NDEBUG
  int res;
  if (lgl->tid >= 0 || !lgl->opts.check.val) return;
  lglpicosatinit (lgl);
  if (lgl->picosat.res) {
    LOG (1, "determined earlier that PicoSAT proved unsatisfiability");
    assert (lgl->picosat.res == 20);
  }
  if (picosat_inconsistent ()) {
    LOG (1, "PicoSAT is already in inconsistent state");
    return;
  }
  if (lgl->assume) picosat_assume (lgl->assume);
  res = picosat_sat (-1);
  assert (res == 20);
  LOG (1, "PicoSAT proved unsatisfiability");
#endif
}
#endif

static void lglunit (LGL * lgl, int lit) {
  assert (!lgl->level);
#ifndef NLGLPICOSAT
  if (lgl->picosat.chk) lglpicosatchkclsarg (lgl, lit, 0);
#endif
  LOG (1, "unit %d", lit);
  lglassign (lgl, lit, (lit << RMSHFT) | UNITCS, 0);
}

static void lglmark (LGL * lgl, int lit) {
  lglavar (lgl, lit)->mark = lglsgn (lit);
}

static void lglunmark (LGL * lgl, int lit) { lglavar (lgl, lit)->mark = 0; }

static void lglchksimpcls (LGL * lgl) {
#ifndef NDEBUG
  int *p, tmp, lit;
  AVar * av;
  for (p = lgl->clause.start; (lit = *p); p++) {
    tmp = lglfixed (lgl, lit);
    assert (!tmp);
    av = lglavar (lgl, lit);
    assert (!av->simp);
    av->simp = 1;
  }
  while (p > lgl->clause.start)
    lglavar (lgl,  *--p)->simp = 0;
#endif
}

static int lglcval (LGL * lgl, int litorval) {
  assert (litorval);
  if (litorval == 1 || litorval == -1) return litorval;
  return lglval (lgl, litorval);
}

static int lglsimpcls (LGL * lgl) {
  int * p, * q = lgl->clause.start, lit, tmp, mark;
  for (p = lgl->clause.start; (lit = *p); p++) {
    tmp = lglcval (lgl, lit);
    if (tmp == 1) { LOG (4, "literal %d satisfies clauses", lit); break; }
    if (tmp == -1) { LOG (4, "removing false literal %d", lit); continue; }
    mark = lglmarked (lgl, lit);
    if (mark > 0)
      { LOG (4, "removing duplicated literal %d", lit); continue; }
    if (mark < 0)
      { LOG (4, "literals %d and %d occur both", -lit, lit); break; }
    *q++ = lit;
    lglmark (lgl, lit);
  }

  *q = 0;
  lgl->clause.top = q + 1;

  while (q > lgl->clause.start) lglunmark (lgl, *--q);

  if (lit) LOG (2, "simplified clause is trivial");
  else LOGCLS (2, lgl->clause.start, "simplified clause");

  return lit;
}

static void lglorderclsaux (LGL * lgl, int * start) {
  int * p, max = 0, level, lit;
  for (p = start; (lit = *p); p++) {
    if (!lglval (lgl, lit)) continue;
    level = lglevel (lgl, lit);
    if (level <= max) continue;
    max = level;
    *p = start[0];
    start[0] = lit;
  }
}

static void lglordercls (LGL * lgl) {
  assert (lglcntstk (&lgl->clause) > 2);
  lglorderclsaux (lgl, lgl->clause.start);
  LOG (3, "head literal %d", lgl->clause.start[0]);
  lglorderclsaux (lgl, lgl->clause.start  + 1);
  LOG (3, "tail literal %d", lgl->clause.start[1]);
  LOGCLS (3, lgl->clause.start, "ordered clause");
}

static void lglfreewch (LGL * lgl, int oldoffset, int oldhcount) {
  int ldoldhcount = lglceilld (oldhcount);
  // assert ((1 << ldoldhcount) <= oldhcount);
  lgl->wchs.start[oldoffset] = lgl->freewchs[ldoldhcount];
  assert (oldoffset);
  lgl->freewchs[ldoldhcount] = oldoffset;
  lgl->nfreewchs++;
  assert (lgl->nfreewchs > 0);
  LOG (4, "saving watch stack at %d of size %d on free list %d",
       oldoffset, oldhcount, ldoldhcount);
}

static void lglshrinkhts (LGL * lgl, HTS * hts, int newcount) {
  int * p, i, oldcount = hts->count;
  assert (newcount <= oldcount);
  if (newcount == oldcount) return;
  p = lglhts2wchs (lgl, hts);
  for (i = newcount; i < oldcount; i++) p[i] = 0;
  hts->count = newcount;
  if (newcount) return;
  lglfreewch (lgl, hts->offset, oldcount);
  hts->offset = 0;
}

static long lglenlwchs (LGL * lgl, HTS * hts) {
  int oldhcount = hts->count, oldoffset = hts->offset, newoffset;
  int oldwcount, newwcount, oldwsize, newwsize, i, j;
  int newhcount = oldhcount ? 2*oldhcount : 1;
  int * oldwstart, * newwstart, * start;
  int ldnewhcount = lglfloorld (newhcount);
  long res = 0;

  newhcount = (1<<ldnewhcount);
  assert (newhcount > oldhcount);

  LOG (4, "increasing watch stack at %d from %d to %d",
       oldoffset, oldhcount, newhcount);

  assert (!oldoffset == !oldhcount);

  lgl->stats.enlwchs++;

  newoffset = lgl->freewchs[ldnewhcount];
  start = lgl->wchs.start;
  if (newoffset != INT_MAX) {
    lgl->freewchs[ldnewhcount] = start[newoffset];
    start[newoffset] = 0;
    assert (lgl->nfreewchs > 0);
    lgl->nfreewchs--;
    LOG (4, "reusing free watch stack at %d of size %d",
         newoffset, (1 << ldnewhcount));
  } else {
    assert (lgl->wchs.start[hts->offset]);
    assert (lgl->wchs.top[-1] == INT_MAX);

    oldwcount = lglcntstk (&lgl->wchs);
    newwcount = oldwcount + newhcount;
    oldwsize = lglszstk (&lgl->wchs);
    newwsize = oldwsize;

    assert (lgl->wchs.top == lgl->wchs.start + oldwcount);
    assert (oldwcount > 0);

    while (newwsize < newwcount) newwsize *= 2;
    if (newwsize > oldwsize) {
      newwstart = oldwstart = lgl->wchs.start;
      RSZ (newwstart, oldwsize, newwsize);
      LOG (3, "resized global watcher stack from %d to %d",
           oldwsize, newwsize);
      res = newwstart - oldwstart;
      if (res) {
	LOG (3, "moved global watcher stack by %ld", res);
	start = lgl->wchs.start = newwstart;
      }
      lgl->wchs.end = start + newwsize;
    }
    lgl->wchs.top = start + newwcount;
    lgl->wchs.top[-1] = INT_MAX;
    newoffset = oldwcount - 1;
    LOG (4,
         "new watch stack of size %d at end of global watcher stack at %d",
         newhcount, newoffset);
  }
  assert (start == lgl->wchs.start);
  assert (start[0]);
  j = newoffset;
  for (i = oldoffset; i < oldoffset + oldhcount; i++) {
    start[j++] = start[i];
    start[i] = 0;
  }
  while (j < newoffset + newhcount)
    start[j++] = 0;
  assert (start + j <= lgl->wchs.top);
  hts->offset = newoffset;
  if (oldhcount > 0) lglfreewch (lgl, oldoffset, oldhcount);
  return res;
}

static long lglpushwch (LGL * lgl, HTS * hts, int wch) {
  long res = 0;
  int * wchs = lglhts2wchs (lgl, hts);
  assert (sizeof (res) == sizeof (void*));
  assert (hts->count >= 0);
  if (wchs[hts->count]) {
    res = lglenlwchs (lgl, hts);
    wchs = lglhts2wchs (lgl, hts);
  }
  assert (!wchs[hts->count]);
  assert (wch != INT_MAX);
  wchs[hts->count++] = wch;
  lgl->stats.pshwchs++;
  assert (lgl->stats.pshwchs > 0);
  return res;
}

static long lglwchbin (LGL * lgl, int lit, int other, int red) {
  HTS * hts = lglhts (lgl, lit);
  int cs = ((other << RMSHFT) | BINCS | red);
  long res;
  assert (red == 0 || red == REDCS);
  res = lglpushwch (lgl, hts, cs);
  LOG (3, "new %s binary watch %d blit %d", lglred2str (red), lit, other);
  return res;
}

static void lglwchtrn (LGL * lgl, int a, int b, int c, int red) {
  HTS * hts = lglhts (lgl, a);
  int cs = ((b << RMSHFT) | TRNCS | red);
  assert (red == 0 || red == REDCS);
  lglpushwch (lgl, hts, cs);
  lglpushwch (lgl, hts, c);
  LOG (3, "new %s ternary watch %d blits %d %d", lglred2str (red), a, b, c);
}

static long lglwchlrg (LGL * lgl, int lit, int other, int red, int lidx) {
  HTS * hts = lglhts (lgl, lit);
  int blit = ((other << RMSHFT) | LRGCS | red);
  long res = 0;
  assert (red == 0 || red == REDCS);
  res += lglpushwch (lgl, hts, blit);
  res += lglpushwch (lgl, hts, lidx);
#ifndef NLGLOG
  {
    int * p = lglidx2lits (lgl, red, lidx);
    LOG (3,
	 "watching %d with blit %d in %s[%d] %d %d %d %d%s",
	 lit, other,
	 (red ? "red" : "irr"), lidx, p[0], p[1], p[2], p[3],
	 (p[4] ? " ..." : ""));
  }
#endif
  assert (sizeof (res) == sizeof (void*));
  return res;
}

static EVar * lglevar (LGL * lgl, int lit) {
  int idx = abs (lit);
  assert (1 < idx && idx < lgl->nvars);
  return lgl->evars + idx;
}

static int * lglepos (LGL * lgl, int lit) {
  EVar * ev;
  int * res;
  ev = lglevar (lgl, lit);
  res = &ev->pos;
  return res;
}

static int lglescore (LGL * lgl, int lit) {
  EVar * ev;
  int res;
  ev = lglevar (lgl, lit);
  res = ev->score;
  return res;
}

static int lglecmp (LGL * lgl, int s, int l, int t, int k) {
  if (s > t) return -1;
  if (s < t) return 1;
  return k - l;
}

#ifndef NDEBUG
static void lglchkesched (LGL * lgl) {
  int * p, parent, child, ppos, cpos, size, i, tmp;
  Stk * s = &lgl->esched;
  int pscr, cscr;
  size = lglcntstk (s);
  p = s->start;
  for (ppos = 0; ppos < size; ppos++) {
    parent = p[ppos];
    tmp = *lglepos (lgl, parent);
    assert (ppos == tmp);
    pscr = lglescore (lgl, parent);
    for (i = 0; i <= 1; i++) {
      cpos = 2*ppos + 1 + i;
      if (cpos >= size) continue;
      child = p[cpos];
      tmp = *lglepos (lgl, child);
      assert (cpos == tmp);
      cscr = lglescore (lgl, child);
      assert (lglecmp (lgl, pscr, parent, cscr, child) >= 0);
    }
  }
}
#endif

static void lgleup (LGL * lgl, int lit) {
  int child = lit, parent, cpos, ppos, * p, * cposptr, * pposptr;
  Stk * s = &lgl->esched;
  int lscr, pscr;
  p = s->start;
  lscr = lglescore (lgl, child);
  cposptr = lglepos (lgl, child);
  cpos = *cposptr;
  assert (cpos >= 0);
  while (cpos > 0) {
    ppos = (cpos - 1)/2;
    parent = p[ppos];
    pscr = lglescore (lgl, parent);
    if (lglecmp (lgl, pscr, parent, lscr, lit) >= 0) break;
    pposptr = lglepos (lgl, parent);
    assert (*pposptr == ppos);
    p[cpos] = parent;
    *pposptr = cpos;
    LOGESCHED (5, parent, "down from %d", ppos);
    cpos = ppos;
    child = parent;
  }
  if (*cposptr == cpos) return;
#ifndef NLGLOG
  ppos = *cposptr;
#endif
  *cposptr = cpos;
  p[cpos] = lit;
  LOGESCHED (5, lit, "up from %d", ppos);
#ifndef NDEBUG
  if (lgl->opts.check.val >= 2) lglchkesched (lgl);
#endif
}

static void lgledown (LGL * lgl, int lit) {
  int parent = lit, child, right, ppos, cpos;
  int * p, * pposptr, * cposptr, size;
  int lscr, cscr, rscr;
  Stk * s = &lgl->esched;
  size = lglcntstk (s);
  p = s->start;
  lscr = lglescore (lgl, parent);
  pposptr = lglepos (lgl, parent);
  ppos = *pposptr;
  assert (0 <= ppos);
  for (;;) {
    cpos = 2*ppos + 1;
    if (cpos >= size) break;
    child = p[cpos];
    cscr = lglescore (lgl, child);
    if (cpos + 1 < size) {
      right = p[cpos + 1];
      rscr = lglescore (lgl, right);
      if (lglecmp (lgl, cscr, child, rscr, right) < 0)
        cpos++, child = right, cscr = rscr;
    }
    if (lglecmp (lgl, cscr, child, lscr, lit) <= 0) break;
    cposptr = lglepos (lgl, child);
    assert (*cposptr = cpos);
    p[ppos] = child;
    *cposptr = ppos;
    LOGESCHED (5, child, "up from %d", cpos);
    ppos = cpos;
    parent = child;
  }
  if (*pposptr == ppos) return;
#ifndef NLGLOG
  cpos = *pposptr;
#endif
  *pposptr = ppos;
  p[ppos] = lit;
  LOGESCHED (5, lit, "down from %d", cpos);
#ifndef NDEBUG
  if (lgl->opts.check.val >= 2) lglchkesched (lgl);
#endif
}

static int lglifrozen (LGL * lgl, int ilit) {
  int elit = lglexport (lgl, ilit);
  Ext * ext = lglelit2ext (lgl, elit);
  return ext->frozen || ext->tmpfrozen;
}

static void lglesched (LGL * lgl, int lit) {
  int * p;
  Stk * s;
  if (lglifrozen (lgl, lit)) return;
  if (!lglisfree (lgl, lit)) return;
  p = lglepos (lgl, lit);
  s = &lgl->esched;
  if (*p >= 0) return;
  *p = lglcntstk (s);
  lglpushstk (lgl, s, lit);
  lgleup (lgl, lit);
  lgledown (lgl, lit);
  LOGESCHED (4, lit, "pushed");
}

static void lgleschedall (LGL * lgl) {
  int lit;
  for (lit = 2; lit < lgl->nvars; lit++)
    lglesched (lgl, lit);
}

static int lglecalc (LGL * lgl, EVar * ev) {
  int res = ev->score, o0 = ev->occ[0], o1 = ev->occ[1];
  if (!o0 || !o1) ev->score = 0;
  else ev->score = o0 + o1;
  return res;
}

static void lglincocc (LGL * lgl, int lit) {
  int idx = abs (lit), old, sign = (lit < 0);
  EVar * ev = lglevar (lgl, lit);
  assert (lglisfree (lgl, lit));
  ev->occ[sign] += 1;
  assert (ev->occ[sign] > 0);
  old = lglecalc (lgl, ev);
  assert (ev->score >= old);
  LOG (3, "inc occ of %d gives escore[%d] = %d with occs %d %d",
       lit, idx, ev->score, ev->occ[0], ev->occ[1], ev->score);
  if (ev->pos < 0) {
    if (lgl->elm.pivot != idx) lglesched (lgl, idx);
  } else if (old < ev->score) lgledown (lgl, idx);
}

static int lglisact (int act) { return NOTALIT <= act && act < REMOVED-1; }

static void lglrescoreglue (LGL * lgl, int glue) {
  int * c, * p, oldact, newact;
  Lir * lir = lgl->red + glue;
  for (c = lir->lits.start; c < lir->lits.top; c = p + 1) {
    oldact = *c;
    if (oldact == REMOVED) {
      for (p = c + 1; p < lir->lits.top && *p == REMOVED; p++)
	;
      assert (p >= lir->lits.top || *p < NOTALIT || lglisact (*p));
      p--;
    } else {
      assert (NOTALIT <= oldact && oldact <= REMOVED - 1);
      newact = NOTALIT + ((oldact - NOTALIT) + 1) / 2;
      *c++ = newact;
      LOGCLS (5, c, "rescoring activity from %d to %d of clause",
              oldact - NOTALIT, newact - NOTALIT);
      for (p = c; *p; p++)
	;
    }
  }
}

static void lglrescoreclauses (LGL * lgl) {
  int glue;
  lgl->stats.rescored.clauses++;
  for (glue = 0; glue < MAXGLUE; glue++)
    lglrescoreglue (lgl, glue);
}

static int lglbumplidx (LGL * lgl, int lidx) {
  int glue = (lidx & GLUEMASK), * c, *ap, act;
  Lir * lir = lgl->red + glue;
  Stk * lits = &lir->lits;
  lidx >>= GLUESHFT;
  c = lits->start + lidx;
  assert (lits->start < c && c < lits->end);
  ap = c - 1;
  act = *ap;
  if (act < REMOVED - 1) {
    lglchkact (act);
    *ap = ++act;
  }
  LOGCLS (4, c, "bumped activity to %d of glue %d clause", act-NOTALIT, glue);
  lgl->stats.lir[glue].resolved++;
  assert (lgl->stats.lir[glue].resolved > 0);
  return (act >= REMOVED - 1);
}

static int lglkeepmaxglue (LGL * lgl) {
  int64_t max, non, sum;
  int mod, shift, rel;
  if (!lgl->opts.keepmaxglue.val) return 0;
  if (lgl->opts.keepmaxglue.val == 1) return 1;
  max = lgl->stats.clauses.maxglue;
  non = lgl->stats.clauses.nonmaxglue;
  sum = max + non;
  rel = sum ? (100*max)/sum : 0;
  mod = lgl->opts.keepmaxglue.val;
  shift = lglceilld (rel)/2;
  mod >>= shift;
  if (mod <= 1) return 1;
  return !(lglrand (lgl) % mod);
}

static void lgladdcls (LGL * lgl, int red, int glue) {
  int size, lit, other, other2, * p, lidx, unit, blit, rescore;
  Lir * lir;
  Val val;
  Stk * w;
  lgl->stats.prgss++;
  assert (!lglmtstk (&lgl->clause));
  assert (!lgl->clause.top[-1]);
  lglchksimpcls (lgl);
#if !defined(NLGLPICOSAT) && !defined(NDEBUG)
  lglpicosataddcls (lgl, lgl->clause.start);
#endif
  size = lglcntstk (&lgl->clause) - 1;
  if (!red) lgl->stats.irr++, assert (lgl->stats.irr > 0);
  else if (size == 2) lgl->stats.red.bin++, assert (lgl->stats.red.bin > 0);
  else if (size == 3) lgl->stats.red.trn++, assert (lgl->stats.red.trn > 0);
  assert (size >= 0);
  if (!size) {
    LOG (1, "found empty clause");
    lgl->mt = 1;
    return;
  }
  lit = lgl->clause.start[0];
  if (size == 1) {
    lglunit (lgl, lit);
    return;
  }
  other = lgl->clause.start[1];
  if (size == 2) {
    lglwchbin (lgl, lit, other, red);
    lglwchbin (lgl, other, lit, red);
    if (red) {
      if (lglval (lgl, lit) < 0) lglf2rce (lgl, other, lit, REDCS);
      if (lglval (lgl, other) < 0) lglf2rce (lgl, lit, other, REDCS);
    } else if (lgl->dense) {
      assert (!red);
      assert (!lgl->level);
      lglincocc (lgl, lit);
      lglincocc (lgl, other);
    }
    return;
  }
  lglordercls (lgl);
  lit = lgl->clause.start[0];
  other = lgl->clause.start[1];
  if (size == 3) {
    other2 = lgl->clause.start[2];
    lglwchtrn (lgl, lit, other, other2, red);
    lglwchtrn (lgl, other, lit, other2, red);
    lglwchtrn (lgl, other2, lit, other, red);
    if (red) {
      if (lglval (lgl, lit) < 0 && lglval (lgl, other) < 0)
	lglf3rce (lgl, other2, lit, other, REDCS);
      if (lglval (lgl, lit) < 0 && lglval (lgl, other2) < 0)
	lglf3rce (lgl, other, lit, other2, REDCS);
      if (lglval (lgl, other) < 0 && lglval (lgl, other2) < 0)
	lglf3rce (lgl, lit, other, other2, REDCS);
    } else if (lgl->dense) {
      assert (!red);
      assert (!lgl->level);
      lglincocc (lgl, lit);
      lglincocc (lgl, other);
      lglincocc (lgl, other2);
    }
    return;
  }
  assert (size > 3);
  if (red) {
    assert (0 <= glue);
    if (glue > 0) glue--;
    switch (lgl->opts.gluescale.val) {
      case 3: glue = glue ? lglceilld (glue) : 0; break;
      case 2: glue = lglceilsqrt32 (glue); break;
      default: assert (glue == 1); //and fall through
      case 1: if (glue > POW2GLUE/2) glue = POW2GLUE/4 + glue/2; break;
    }
    assert (0 <= glue);
    if (glue >= MAXGLUE) glue = MAXGLUE;
    lgl->stats.clauses.scglue += glue;
    if (glue == MAXGLUE) {
        lgl->stats.clauses.maxglue++;
        if (lglkeepmaxglue (lgl)) {
	  lgl->stats.clauses.keptmaxglue++;
	  glue--;
	}
    } else lgl->stats.clauses.nonmaxglue++;
    lir = lgl->red + glue;
    w = &lir->lits;
    lidx = lglcntstk (w) + 1;
    if (lidx > MAXREDLIDX) {
      if (glue == MAXGLUE) {
	lglbacktrack (lgl, 0);
	lidx = lglcntstk (w);
	assert (!lidx);
      }
      while (glue > 0 && lidx > MAXREDLIDX) {
	lir = lgl->red + --glue;
	w = &lir->lits;
	lidx = lglcntstk (w) + 1;
      }
      if (lidx > MAXREDLIDX)
	lgldie ("number of redundant large clause literals exhausted");
    }
    lglpushstk (lgl, w, NOTALIT);
    assert (lidx == lglcntstk (w));
    lidx <<= GLUESHFT;
    assert (0 <= lidx);
    lidx |= glue;
    lgl->stats.lir[glue].clauses++;
    assert (lgl->stats.lir[glue].clauses > 0);
    lgl->stats.lir[glue].added++;
    assert (lgl->stats.lir[glue].added > 0);
  } else {
    w = &lgl->irr;
    lidx = lglcntstk (w);
    if (lidx <= 0 && !lglmtstk (w))
      lgldie ("number of irredundant large clause literals exhausted");
  }
  for (p = lgl->clause.start; (other2 = *p); p++)
    lglpushstk (lgl, w, other2);
  lglpushstk (lgl, w, 0);
  if (red) {
    unit = 0;
    for (p = lgl->clause.start; (other2 = *p); p++) {
      val = lglval (lgl, other2);
      assert (val <= 0);
      if (val < 0) continue;
      if (unit) unit = INT_MAX;
      else unit = other2;
    }
    if (unit && unit != INT_MAX) lglflrce (lgl, unit, red, lidx);
  }
  assert (red == 0 || red == REDCS);
  if ((!red && !lgl->dense) || (red && glue < MAXGLUE)) {
    (void) lglwchlrg (lgl, lit, other, red, lidx);
    (void) lglwchlrg (lgl, other, lit, red, lidx);
  }
  if (red && glue != MAXGLUE) {
    lgl->stats.red.lrg++;
    lgl->stats.rdded++;
    rescore = lglbumplidx (lgl, lidx);
    assert (!rescore);
  }
  if (!red && lgl->dense) {
    assert (!lgl->level);
    if (lidx > MAXIRRLIDX)
      lgldie ("number of irredundant large clause literals exhausted");
    blit = (lidx << RMSHFT) | IRRCS;
    for (p = lgl->clause.start; (other2 = *p); p++) {
      lglincocc (lgl, other2);
      lglpushwch (lgl, lglhts (lgl, other2), blit);
    }
  }
}

static void lgliadd (LGL * lgl, int ilit) {
#ifndef NLGLOG
  if (lglmtstk (&lgl->clause)) LOG (4, "opening irredundant clause");
#endif
  assert (abs (ilit) < 2 || abs (ilit) < lgl->nvars);
  lglpushstk (lgl, &lgl->clause, ilit);
  if (ilit) {
    LOG (4, "added literal %d", ilit);
  } else {
    LOG (4, "closing irredundant clause");
    LOGCLS (3, lgl->clause.start, "unsimplified irredundant clause");
    if (!lglsimpcls (lgl)) lgladdcls (lgl, 0, 0);
    lglclnstk (&lgl->clause);
  }
}

static void lgldepart (LGL * lgl) {
  int idx;
  assert (lgl->partitioned);
  LOG (2, "departitioning");
  for (idx = 2; idx < lgl->nvars; idx++)
    lglavar (lgl, idx)->part = 0;
  lgldreschedule (lgl);
  lgl->partitioned = 0;
}

static void lglreset (LGL * lgl) {
  if (lgl->state == RESET) return;
  if (lgl->state <= USED) return;
  assert (lgl->state & (UNKNOWN | SATISFIED | EXTENDED | UNSATISFIED));
  if (lgl->partitioned) lgldepart (lgl);
  if (lgl->level > 0) lglbacktrack (lgl, 0);
  if (lgl->assume) {
    LOG (2, "resetting assumption %d", lgl->assume);
    lgl->failed = lgl->eassume = lgl->assume = 0;
  }
#if !defined(NDEBUG) && !defined (NLGLPICOSAT)
  if (lgl->picosat.res) {
    LOG (2, "resetting earlier PicoSAT result %d", lgl->picosat.res);
    lgl->picosat.res = 0;
  }
#endif
  TRANS (RESET);
}

static void lgluse (LGL * lgl) {
  if (lgl->state >= USED) return;
  assert (lgl->state == UNUSED || lgl->state == OPTSET);
  TRANS (USED);
}

void lgladd (LGL * lgl, int elit) {
  int ilit, eidx = abs (elit);
  Ext * ext;
  TRAPI ("add %d", elit);
  lgl->stats.calls.add++;
  ABORTIF (!lgl, "can not add literal with uninitialized manager");
  if (0 < eidx && eidx <= lgl->maxext) {
    ext = lglelit2ext (lgl, elit);
    ABORTIF (ext->melted, "adding melted literal %d", elit);
  }
  lglreset (lgl);
  if (elit) {
    ilit = lglimport (lgl, elit);
    LOG (4, "adding external literal %d as %d", elit, ilit);
  } else {
    ilit = 0;
    LOG (4, "closing external clause");
  }
  lgliadd (lgl, ilit);
#ifndef NCHKSOL
  lglpushstk (lgl, &lgl->orig, elit);
#endif
  lgluse (lgl);
}

void lglassume (LGL * lgl, int elit) {
  int ilit, eidx = abs (elit);
  Ext * ext;
  TRAPI ("assume %d", elit);
  lgl->stats.calls.assume++;
  ABORTIF (!elit, "can not assume invalid literal 0");
  ABORTIF (!lgl, "can not assume literal with uninitialized manager");
  ABORTIF (lgl->assume, "multiple assumptions not implemented yet");
  assert (!lgl->eassume);
  if (0 < eidx && eidx <= lgl->maxext) {
    ext = lglelit2ext (lgl, elit);
    ABORTIF (ext->melted, "assuming melted literal %d", elit);
  }
  lglreset (lgl);
  ilit = lglimport (lgl, elit);
  LOG (2, "assuming external literal %d as %d", elit, ilit);
  lgl->eassume = elit;
  lgl->assume = ilit;
  assert (!lgl->failed);
  lgluse (lgl);
}

static void lglbonflict (LGL * lgl, int lit, int blit) {
  assert (lglevel (lgl, lit) >= lglevel (lgl, blit >> RMSHFT));
  assert (!lgliselim (lgl, blit >> RMSHFT));
  assert (!lgliselim (lgl, lit));
  lgl->conf.lit = lit;
  lgl->conf.rsn[0] = blit;
  LOG (2, "inconsistent %s binary clause %d %d",
       lglred2str (blit & REDCS), lit, (blit >> RMSHFT));
}

static void lgltonflict (LGL * lgl, int lit, int blit, int other2) {
  assert ((blit & MASKCS) == TRNCS);
  assert (lglevel (lgl, lit) >= lglevel (lgl, blit >> RMSHFT));
  assert (lglevel (lgl, lit) >= lglevel (lgl, other2));
  assert (!lgliselim (lgl, blit >> RMSHFT));
  assert (!lgliselim (lgl, other2));
  assert (!lgliselim (lgl, lit));
  lgl->conf.lit = lit;
  lgl->conf.rsn[0] = blit;
  lgl->conf.rsn[1] = other2;
  LOG (2, "inconsistent %s ternary clause %d %d %d",
       lglred2str (blit & REDCS), lit, (blit>>RMSHFT), other2);
}

static void lglonflict (LGL * lgl,
                         int check,
                         int lit, int red, int lidx) {
  Lir * lir;
  int glue;
#if !defined (NLGLOG) || !defined (NDEBUG)
  int * p, * c = lglidx2lits (lgl, red, lidx);
#endif
  assert (red == REDCS || !red);
#ifndef NDEBUG
  {
    int found = 0;
    for (p = c; *p; p++) {
      if(*p == lit) found++;
      assert (lglval (lgl, *p) <= -check);
      assert (lglevel (lgl, lit) >= lglevel (lgl, *p));
      assert (!lgliselim (lgl, lit));
    }
    assert (found == 1);
  }
#endif
  lgl->conf.lit = lit;
  lgl->conf.rsn[0] = red | LRGCS;
  lgl->conf.rsn[1] = lidx;
#ifndef NLGLOG
  if (lgl->opts.log.val >= 2) {
    lglogstart (lgl, 2, "inconsistent %s large clause", lglred2str (red));
    for (p = c ; *p; p++)
      printf (" %d", *p);
    lglogend (lgl);
  }
#endif
  if (red) {
    glue = lidx & GLUEMASK;
    lir = lgl->red + glue;
    lgl->stats.lir[glue].conflicts++;
    assert (lgl->stats.lir[glue].conflicts > 0);
    if (glue != MAXGLUE) lgl->stats.ronflicts++;
  }
}

static void lgldeclscnt (LGL * lgl, int size, int red, int glue) {
  assert (!red || red == REDCS);
  if (!red) { assert (lgl->stats.irr); lgl->stats.irr--; }
  else if (size == 2) { assert (lgl->stats.red.bin); lgl->stats.red.bin--; }
  else if (size == 3) { assert (lgl->stats.red.trn); lgl->stats.red.trn--; }
  else {
    assert (lgl->stats.red.lrg > 0);
    lgl->stats.red.lrg--;
    assert (lgl->stats.lir[glue].clauses > 0);
    lgl->stats.lir[glue].clauses--;
  }
}

static void lglrmtwch (LGL * lgl, int lit, int other1, int other2, int red) {
  int * p, blit, other, blit1, blit2, * w, * eow, tag;
  HTS * hts;
  assert (!red || red == REDCS);
  LOG (3, "removing %s ternary watch %d blits %d %d",
       lglred2str (red), lit, other1, other2);
  hts = lglhts (lgl, lit);
  assert (hts->count >= 2);
  p = w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  blit1 = (other1 << RMSHFT) | red | TRNCS;
  blit2 = (other2 << RMSHFT) | red | TRNCS;
  for (;;) {
    assert (p < eow);
    if (p == eow) return;	// TODO remove this
    blit = *p++;
    tag = blit & MASKCS;
    if (tag == BINCS) continue;
    if (tag == IRRCS) { assert (lgl->dense); continue; }
    other = *p++;
    if (blit == blit1 && other == other2) break;
    if (blit == blit2 && other == other1) break;
  }
  while (p < eow) p[-2] = p[0], p++;
  lglshrinkhts (lgl, hts, p - w - 2);
}

static int lglca (LGL * lgl, int a, int b) {
  int c, res, prev, r0, tag, * rsn;
  AVar * av;
  assert (abs (a) != abs (b));
  assert (lglval (lgl, a) > 0 && lglval (lgl, b) > 0);
  assert (lglevel (lgl, a) == lglevel (lgl, b));
  assert (lgldom (lgl, a) == lgldom (lgl, b));
  res = 0;
  for (c = a; c; c = -prev) {
    assert (lglval (lgl, c) > 0);
    av = lglavar (lgl, c);
    assert (!av->mark);
    av->mark = 1;
    rsn = lglrsn (lgl, c);
    r0 = rsn[0];
    tag = r0 & MASKCS;
    if (tag != BINCS) break;
    prev = r0 >> RMSHFT;
    assert (prev || c == lgl->decision);
  }
  for (res = b; res; res = -prev) {
    assert (lglval (lgl, res) > 0);
    av = lglavar (lgl, res);
    if (av->mark) break;
    rsn = lglrsn (lgl, res);
    r0 = rsn[0];
    tag = r0 & MASKCS;
    if (tag != BINCS) { res = 0; break; }
    prev = r0 >> RMSHFT;
  }
  for (c = a; c; c = -prev) {
    assert (lglval (lgl, c) > 0);
    av = lglavar (lgl, c);
    assert (av->mark);
    av->mark = 0;
    rsn = lglrsn (lgl, c);
    r0 = rsn[0];
    tag = r0 & MASKCS;
    if (tag != BINCS) break;
    prev = r0 >> RMSHFT;
  }
  LOG (3, "least common ancestor of %d and %d is %d", a, b, res);
  assert (res);//NOTE: specialized to the usage of this function
  return res;
}

static void lglrmlwch (LGL * lgl, int lit, int red, int lidx) {
  int blit, tag, * p, * q, * w, * eow, ored, olidx;
  HTS * hts;
  assert (!lgl->dense || red);
#ifndef NLGLOG
  p = lglidx2lits (lgl, red, lidx);
  LOG (3, "removing watch %d in %s[%d] %d %d %d %d%s",
       lit, (red ? "red" : "irr"), lidx, p[0], p[1], p[2], p[3],
       (p[4] ? " ..." : ""));
#endif
  hts = lglhts (lgl, lit);
  assert (hts->count >= 2);
  p = w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  for (;;) {
    assert (p < eow);
    if (p == eow) return;	// TODO remove this
    blit = *p++;
    tag = blit & MASKCS;
    if (tag == BINCS) continue;
    if (tag == IRRCS) { assert (lgl->dense); continue; }
    olidx = *p++;
    if (tag == TRNCS) continue;
    assert (tag == LRGCS);
    ored = blit & REDCS;
    if (ored != red) continue;
    if (olidx == lidx) break;
  }
  assert ((p[-2] & REDCS) == red);
  assert (p[-1] == lidx);
  for (q = p; q < eow; q++)
    q[-2] = q[0];

  lglshrinkhts (lgl, hts, q - w - 2);
}

static void lglpropsearch (LGL * lgl, int lit) {
  int * q, * eos, blit, other, other2, other3, red, prev;
  int tag, val, val2, lidx, * c, * l, tmp = INT_MAX;
  const int * p;
  long delta;
  int visits;
  HTS * hts;
  assert (!lgl->simp);
  assert (!lgl->distilling);
  assert (!lgl->probing);
  assert (!lgl->dense);
  assert (lgl->propred);
  LOG (3, "propagating %d in search", lit);
  assert (!lgliselim (lgl, lit));
  assert (lglval (lgl, lit) == 1);
  hts = lglhts (lgl, -lit);
  if (!hts->offset) return;
  q = lglhts2wchs (lgl, hts);
  assert (hts->count >= 0);
  eos = q + hts->count;
  visits = 0;
  for (p = q; p < eos; p++) {
    visits++;
    *q++ = blit = *p;
    tag = blit & MASKCS;
    if (tag != BINCS) {
      assert (tag == TRNCS || tag == LRGCS);
      *q++ = tmp = *++p;
    } else assert ((tmp = INT_MAX));
    other = (blit >> RMSHFT);
    val = lglval (lgl, other);
    if (val > 0) continue;
    red = blit & REDCS;
    if (tag == BINCS) {
      assert (!red || !lgliselim (lgl, other));
      if (val < 0) {
	lglbonflict (lgl, -lit, blit);
	p++;
	break;
      }
      assert (!val);
      lglf2rce (lgl, other, -lit, red);
    } else if (tag == TRNCS) {
      assert (tmp != INT_MAX);
      other2 = tmp;
      assert (val <= 0);
      assert (!red || !lgliselim (lgl, other));
      val2 = lglval (lgl, other2);
      if (val2 > 0) continue;
      if (!val && !val2) continue;
	assert (!red || !lgliselim (lgl, other2));
      if (val < 0 && val2 < 0) {
	lgltonflict (lgl, -lit, blit, other2);
	p++;
	break;
      }
      if (!val) { tmp = other2; other2 = other; other = tmp; }
      else assert (val < 0);
      lglf3rce (lgl, other2, -lit, other, red);
    } else {
      assert (tmp != INT_MAX);
      assert (tag == LRGCS);
      assert (val <= 0);
      lidx = tmp;
      c = lglidx2lits (lgl, red, lidx);
      other2 = c[0];
      if (other2 == -lit) other2 = c[0] = c[1], c[1] = -lit;
      if (other2 != other) {
	other = other2;
	val = lglval (lgl, other);
	if (val > 0) {
	  q[-2] = LRGCS | (other2 << RMSHFT) | red;
	  continue;
	}
      }
      assert (!red || !lgliselim (lgl, other));
      val2 = INT_MAX;
      prev = -lit;
      for (l = c + 2; (other2 = *l); l++) {
	*l = prev;
	val2 = lglval (lgl, other2);
	if (val2 >= 0) break;
	assert (!red || !lgliselim (lgl, other));
	prev = other2;
      }
      assert (val2 != INT_MAX);
      if (other2 && val2 >= 0) {
	c[1] = other2;
	assert (other == c[0]);
	delta = lglwchlrg (lgl, other2, other, red, lidx);
	if (delta) p += delta, q += delta, eos += delta;
	q -= 2;
	continue;
      }
      while (l > c + 2) {
	other3 = *--l;
	*l = prev;
	prev = other3;
      }
      if (other2 && val2 < 0) continue;
      if (val < 0) {
	lglonflict (lgl, 1, -lit, red, lidx);
	p++;
	break;
      }
      assert (!val);
      lglflrce (lgl, other, red, lidx);
    }
  }
  while (p < eos) *q++ = *p++;
  lglshrinkhts (lgl, hts, hts->count - (p - q));
  lgl->stats.visits.search += visits;
}

static int lglhbred (LGL * lgl, int subsumed, int red) {
  int res = subsumed ? red : REDCS;
  LOG (3, "hyber binary learned clause becomes %s", lglred2str (res));
  return res;
}

static void lglprop (LGL * lgl, int lit) {
  int tag, val, val2, lidx, * c, * l, tmp, igd, dom, hbred, subsumed, unit;
  int * p, * q, * eos, blit, other, other2, other3, red, prev, i0, i1, i2;
  int glue, visits;
  long delta;
  HTS * hts;
  LOG (3, "propagating %d over ternary and large clauses", lit);
  assert (!lgliselim (lgl, lit));
  assert (lglval (lgl, lit) == 1);
  hts = lglhts (lgl, -lit);
  if (!hts->offset) return;
  q = lglhts2wchs (lgl, hts);
  assert (hts->count >= 0);
  eos = q + hts->count;
  visits = 0;
  igd = 0;
  for (p = q; p < eos; p++) {
    visits++;
    blit = *p;
    tag = blit & MASKCS;
    if (tag == IRRCS) {
      assert (lgl->dense);
      *q++ = blit;
      lidx = blit >> RMSHFT;
      c = lglidx2lits (lgl, 0, lidx);
      unit = 0;
      for (l = c; (other = *l); l++) {
	val = lglval (lgl, other);
	if (val > 0) break;
	if (val < 0) continue;
	if (unit) break;
	unit = other;
      }
      if (other) continue;
      if (unit) { lglflrce (lgl, unit, 0, lidx); continue; }
      lglonflict (lgl, 1, -lit, 0, lidx);
      p++;
      break;
    }
    red = blit & REDCS;
    other = (blit >> RMSHFT);
    val = lglval (lgl, other);
    if (tag == BINCS) {
      *q++ = blit;
      if (val > 0) continue;
      if (red) {
	if (!lgl->propred) continue;
	if (lgliselim (lgl, other)) continue;
      }
      if (val < 0) {
	lglbonflict (lgl, -lit, blit);
	p++;
	break;
      }
      assert (!val);
      lglf2rce (lgl, other, -lit, red);
    } else if (tag == TRNCS) {
      *q++ = blit;
      other2 = *++p;
      *q++ = other2;
      if (val > 0) continue;
      if (red) {
	if (!lgl->propred) continue;
	if (lgliselim (lgl, other)) continue;
      }
      val2 = lglval (lgl, other2);
      if (val2 > 0) continue;
      if (!val && !val2) continue;
      if (red && lgliselim (lgl, other2)) continue;
      if (lgl->igntrn && !igd) {
	i0 = lgl->ignlits[0], i1 = lgl->ignlits[1], i2 = lgl->ignlits[2];
	if (i0 == -lit) {
	  if (i1 == other) { if (i2 == other2) { igd = 1; continue; } }
	  else if (i2 == other) { if (i1 == other2) { igd = 1; continue; } }
	} else if (i1 == -lit) {
	  if (i0 == other) { if (i2 == other2) { igd = 1; continue; } }
	  else if (i2 == other) { if (i0 == other2) { igd = 1; continue; } }
	} else if (i2 == -lit) {
	  if (i0 == other) { if (i1 == other2) { igd = 1; continue; } }
	  else if (i1 == other) { if (i0 == other2) { igd = 1; continue; } }
	}
      }
      if (val < 0 && val2 < 0) {
	lgltonflict (lgl, -lit, blit, other2);
	p++;
	break;
      }
      if (!val) { tmp = other2; other2 = other; other = tmp; }
      else assert (val < 0);
      if (lgl->opts.lhbr.val && lgl->level >= 1) {
	assert (lgl->simp);
	if (lglevel (lgl, other) < 1) dom = lit;
	else {
	  dom = lgldom (lgl, lit);
	  if (lgldom (lgl, -other) != dom) goto NO_HBR_JUST_F3RCE;
	  dom = lglca (lgl, lit, -other);
	}
	subsumed = (dom == lit || dom == -other);
	if (subsumed && lgl->distilling) goto NO_HBR_JUST_F3RCE;
	hbred = lglhbred (lgl, subsumed, red);
 	LOG (2, "hyper binary resolved %s clause %d %d",
	     lglred2str (hbred), -dom, other2);
#ifndef NLGLPICOSAT
	lglpicosatchkclsarg (lgl, -dom, other2, 0);
#endif
	if (subsumed) {
	  LOG (2, "subsumes %s ternary clause %d %d %d",
	       lglred2str (red), -lit, other, other2);
	  lglrmtwch (lgl, other2, other, -lit, red);
	  lglrmtwch (lgl, other, other2, -lit, red);
	  lgl->stats.hbr.sub++;
	  if (red) assert (lgl->stats.red.trn), lgl->stats.red.trn--;
	  else assert (lgl->stats.irr), lgl->stats.irr--;
	}
	delta = 0;
	if (dom == lit) {
	  LOG (3,
	  "replacing %s ternary watch %d blits %d %d with binary %d blit %d",
	  lglred2str (red), -lit, other, other2, -lit, -dom);
	  assert (subsumed);
	  blit = (other2 << RMSHFT) | BINCS | hbred;
	  q[-2] = blit;
	  q--;
	} else {
	  if (dom == -other) {
	    LOG (3, "removing %s ternary watch %d blits %d %d",
		 lglred2str (red), -lit, other, other2);
	    assert (subsumed);
	    q -= 2;
	  } else {
	    LOG (2, "replaces %s ternary clause %d %d %d as reason for %d",
		 lglred2str (red), -lit, other, other2, other2);
	    assert (!subsumed);
	    assert (abs (dom) != abs (lit));
	    assert (abs (other2) != abs (lit));
	  }
	  delta += lglwchbin (lgl, -dom, other2, hbred);
	}
	delta += lglwchbin (lgl, other2, -dom, hbred);
	if (delta) p += delta, q += delta, eos += delta;
	if (hbred) lgl->stats.red.bin++, assert (lgl->stats.red.bin > 0);
	else lgl->stats.irr++, assert (lgl->stats.irr > 0);
	lglf2rce (lgl, other2, -dom, hbred);
	lgl->stats.hbr.trn++;
	lgl->stats.hbr.cnt++;
      } else {
NO_HBR_JUST_F3RCE:
       lglf3rce (lgl, other2, -lit, other, red);
      }
    } else {
      assert (tag == LRGCS);
      assert (!lgl->dense || red);
      if (val > 0) goto COPYL;
      if (red && !lgl->propred) goto COPYL;
      lidx = p[1];
      if (lidx == lgl->ignlidx) goto COPYL;
      c = lglidx2lits (lgl, red, lidx);
      other2 = c[0];
      if (other2 == -lit) other2 = c[0] = c[1], c[1] = -lit;
      if (other2 != other) {
	other = other2;
	val = lglval (lgl, other);
	blit = red;
	blit |= LRGCS;
	blit |= other2 << RMSHFT;
	if (val > 0) goto COPYL;
      }
      if (red && lgliselim (lgl, other)) goto COPYL;
      val2 = INT_MAX;
      prev = -lit;
      for (l = c + 2; (other2 = *l); l++) {
	*l = prev;
	val2 = lglval (lgl, other2);
	if (val2 >= 0) break;
	if (red && lgliselim (lgl, other2)) break;
	prev = other2;
      }

      assert (val2 != INT_MAX);
      if (other2 && val2 >= 0) {
	c[1] = other2;
	assert (other == c[0]);
	delta = lglwchlrg (lgl, other2, other, red, lidx);
	if (delta) p += delta, q += delta, eos += delta;
	p++;
	continue;
      }

      while (l > c + 2) {
	other3 = *--l;
	*l = prev;
	prev = other3;
      }

      if (other2 && val2 < 0) goto COPYL;

      if (val < 0) {
	lglonflict (lgl, 1, -lit, red, lidx);
	break;
      }

      assert (!val);
      if (lgl->opts.lhbr.val && lgl->level >= 1) {
	assert (lgl->simp);
	dom = 0;
	for (l = c; (other2 = *l); l++) {
	  if (other2 == other) continue;
	  if (!lglevel (lgl, other2)) continue;
	  assert (lglval (lgl, other2) < 0);
	  if (!dom) dom = lgldom (lgl, other);
	  if (dom != lgldom (lgl, other2)) goto NO_HBR_JUST_FLRCE;
	}
	LOGCLS (2, c, "dominator %d for %s clause", dom, lglred2str (red));
	dom = lit;
	for (l = c; (other2 = *l); l++) {
	  if (other2 == other) continue;
	  assert (lglval (lgl, other2) < 0);
	  if (other2 == -lit) continue;
	  if (lglevel (lgl, other2) < 1) continue;
	  if (dom == -other2) continue;
	  dom = lglca (lgl, dom, -other2);
	}
	LOGCLS (2, c, "closest dominator %d", dom);
	subsumed = 0;
	for (l = c; !subsumed && (other2 = *l); l++)
	  subsumed = (dom == -other2);
	if (subsumed && lgl->distilling) goto NO_HBR_JUST_FLRCE;
	assert (lit != dom || subsumed);
	hbred = lglhbred (lgl, subsumed, red);
 	LOG (2, "hyper binary resolved %s clause %d %d",
	     lglred2str (hbred), -dom, other);
#ifndef NLGLPICOSAT
	lglpicosatchkclsarg (lgl, -dom, other, 0);
#endif
	if (subsumed) {
	  LOGCLS (2, c, "subsumes %s large clause", lglred2str (red));
	  lglrmlwch (lgl, other, red, lidx);
	  lgl->stats.hbr.sub++;
	  if (red) {
	    glue = lidx & GLUEMASK;
	    if (glue != MAXGLUE) {
	      assert (lgl->stats.red.lrg);
	      lgl->stats.red.lrg--;
	      assert (lgl->stats.lir[glue].clauses > 0);
	      lgl->stats.lir[glue].clauses--;
	    }
	  } else assert (lgl->stats.irr), lgl->stats.irr--;
	  if (red && glue < MAXGLUE) { lglchkact (c[-1]); c[-1] = REMOVED; }
	  for (l = c; *l; l++) *l = REMOVED;
	  *l = REMOVED;
	}
	delta = 0;
	if (dom == lit) {
	  assert (subsumed);
	  LOG (3,
	       "replacing %s large watch %d with binary watch %d blit %d",
	       lglred2str (red), -lit, -lit, -dom);
	  blit = (other << RMSHFT) | BINCS | hbred;
	  *q++ = blit, p++;
	} else {
	  if (subsumed) {
	    LOG (3, "removing %s large watch %d", lglred2str (red), -lit);
	    p++;
	  } else {
	    LOGCLS (2, c,
	            "%s binary clause %d %d becomes reasons "
		    "for %d instead of %s large clause",
	            lglred2str (hbred), -dom, other, other, lglred2str (red));
	    assert (hbred == REDCS);
	  }
	  delta += lglwchbin (lgl, -dom, other, hbred);
	}
	delta += lglwchbin (lgl, other, -dom, hbred);
	if (delta) p += delta, q += delta, eos += delta;
	if (hbred) lgl->stats.red.bin++, assert (lgl->stats.red.bin > 0);
	else lgl->stats.irr++, assert (lgl->stats.irr > 0);
	lglf2rce (lgl, other, -dom, hbred);
	lgl->stats.hbr.lrg++;
	lgl->stats.hbr.cnt++;
	if (subsumed) continue;
      } else {
NO_HBR_JUST_FLRCE:
	lglflrce (lgl, other, red, lidx);
      }
COPYL:
      *q++ = blit;
      *q++ = *++p;
    }
  }
  while (p < eos) *q++ = *p++;
  lglshrinkhts (lgl, hts, hts->count - (p - q));
}

static void lglprop2 (LGL * lgl, int lit) {
  int other, blit, tag, val, red, visits;
  const int * p, * w, * eow;
  HTS * hts;
  assert (lgl->propred || lgl->distilling);
  LOG (3, "propagating %d over binary clauses", lit);
  assert (!lgliselim (lgl, lit));
  assert (lglval (lgl, lit) == 1);
  visits = 0;
  hts = lglhts (lgl, -lit);
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  for (p = w; p < eow; p++) {
    visits++;
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag != BINCS) continue;
    red = blit & REDCS;
    if (red && !lgl->propred) continue;
    other = blit >> RMSHFT;
    assert (!lgliselim (lgl, other));
    val = lglval (lgl, other);
    if (val > 0) continue;
    if (val < 0) { lglbonflict (lgl, -lit, blit); break; }
    lglf2rce (lgl, other, -lit, red);
  }
  if (lgl->simp) lgl->stats.visits.simp += visits;
  else lgl->stats.visits.search += visits;
}

static int lglbcp (LGL * lgl) {
  int lit, cnt, next2 = lgl->next, count = 0;
  assert (!lgl->mt && !lgl->conf.lit && !lgl->failed);
  while (!lgl->conf.lit) {
    cnt = lglcntstk (&lgl->trail);
    if (next2 < cnt) {
      lit = lglpeek (&lgl->trail, next2++);
      lglprop2 (lgl, lit);
      continue;
    }
    if (lgl->next >= cnt) break;
    lit = lglpeek (&lgl->trail, lgl->next++);
    count++;
    lglprop (lgl, lit);
  }
  if (lgl->simp) lgl->stats.props.simp += count;
  else lgl->stats.props.search += count;

  return !lgl->conf.lit;
}

static int lglbcpsearch (LGL * lgl) {
  int lit, count = 0;
  assert (!lgl->simp);
  assert (!lgl->mt && !lgl->conf.lit);
  while (!lgl->conf.lit && lgl->next < lglcntstk (&lgl->trail)) {
    lit = lglpeek (&lgl->trail, lgl->next++);
    lglpropsearch (lgl, lit);
    count++;
  }
  lgl->stats.props.search += count;
  return !lgl->conf.lit;
}

#ifndef NDEBUG
static void lglchkclnvar (LGL * lgl) {
  AVar * av;
  int i;
  for (i = 2; i < lgl->nvars; i++) {
    av = lglavar (lgl, i);
    assert (!av->mark);
  }
}
#endif

#ifdef RESOLVENT
static int lglmaintainresolvent (LGL * lgl) {
#ifndef NDEBUG
  if (lgl->opts.check.val >= 1) return 1;
#endif
#ifndef NLGLOG
  if (lgl->opts.log.val >= 2) return 1;
#endif
  return 0;
}
#endif

static int lgldecision (LGL * lgl, int lit) {
  int * rsn = lglrsn (lgl, lit);
  int tag = rsn[0] & MASKCS;
  return tag == DECISION;
}

static int lgldscheduled (LGL * lgl, int lit) {
  return lglavar (lgl, lit)->pos >= 0;
}

static int lglbumplit (LGL * lgl, int lit) {
  int idx = abs (lit);
  AVar * av = lglavar (lgl, idx);
  Flt oldscore, newscore;
  assert (lglval (lgl, lit) < 0);
  oldscore = av->score;
  newscore = lgladdflt (oldscore, lgl->scinc);
  av->score = newscore;
  LOG (3, "bumping decision score of variable %d from %s to %s",
       idx, lglflt2str (lgl, oldscore), lglflt2str (lgl, newscore));
  assert (newscore > oldscore);
  if (lgldscheduled (lgl, idx)) lgldup (lgl, idx);
  return (newscore >= lgl->maxscore);
}

static int lglpull (LGL * lgl, int lit, int * rescore) {
  AVar * av = lglavar (lgl, lit);
  int level, res;
  if (av->mark) return 0;
  level = lglevel (lgl, lit);
  if (!level) return 0;
  av->mark = 1;
  lglpushstk (lgl, &lgl->seen, lit);
#ifdef RESOLVENT
  if (lglmaintainresolvent (lgl)) {
    lglpushstk (lgl, &lgl->resolvent, lit);
    LOG (2, "adding %d to resolvent", lit);
    LOGRESOLVENT (3, "resolvent after adding %d is", lit);
  }
#endif
  if (level == lgl->level) {
    LOG (2, "reason literal %d at same level %d", lit, lgl->level);
    res = 1;
  } else {
    lglpushstk (lgl, &lgl->clause, lit);
    LOG (2, "adding literal %d at upper level %d to 1st UIP clause",
	 lit, lglevel (lgl, lit));
    if (!lglevelused (lgl, level)) {
      lgluselevel (lgl, level);
      lglpushstk (lgl, &lgl->frames, level);
      LOG (2, "pulled in decision level %d", level);
    }
    res = 0;
  }
  *rescore = lglbumplit (lgl, lit);
  return res;
}

static int lglpoison (LGL * lgl, int lit) {
  AVar * av = lglavar (lgl, lit);
  int level, res;
  if (av->mark) res = 0;
  else {
    level = lglevel (lgl, lit);
    if (!level) res = 0;
    else {
      assert (level < lgl->level);
      if (lgldecision (lgl, lit)) res = 1;
      else if (!lglevelused (lgl, level)) res = 1;
      else {
	lgl->stats.poison.search++;
	if (av->poisoned) {
	  lgl->stats.poison.hits++;
	  res = 1;
	} else {
	  av->mark = 1;
	  lglpushstk (lgl, &lgl->seen, lit);
	  res = 0;
	}
      }
    }
  }
  if (res && !av->poisoned) {
    av->poisoned = 1;
    lglpushstk (lgl, &lgl->poisoned, lit);
  }
  return res;
}

static int lglmincls (LGL * lgl, int start, int * lptr) {
  int lit, tag, r0, r1, other, * p, * q, *top, old, next;
  int limit = *lptr, poisoned, * rsn;
  AVar * av, * bv;
  if (limit <= 0) return 0;
  assert (lglmarked (lgl, start));
  lit = start;
  av = lglavar (lgl, lit);
  rsn = lglrsn (lgl, lit);
  r0 = rsn[0];
  tag = (r0 & MASKCS);
  if (tag == DECISION) return 0;
  old = next = lglcntstk (&lgl->seen);
  for (;;) {
    if (limit-- <= 0) goto FAILED;
    r1 = rsn[1];
    if (tag == BINCS || tag == TRNCS) {
      other = r0 >> RMSHFT;
      if (lglpoison (lgl, other)) goto FAILED;
      if (tag == TRNCS && lglpoison (lgl, r1)) goto FAILED;
    } else {
      assert (tag == LRGCS);
      p = lglidx2lits (lgl, (r0 & REDCS), r1);
      while ((other = *p++))
	if (other != -lit && lglpoison (lgl, other)) goto FAILED;
    }
    if (next == lglcntstk (&lgl->seen)) {
      *lptr = limit;
      return 1;
    }
    lit = lglpeek (&lgl->seen, next++);
    av = lglavar (lgl, lit);
    assert (av->mark);
    rsn = lglrsn (lgl, lit);
    r0 = rsn[0];
    tag = (r0 & MASKCS);
  }
FAILED:
  *lptr = limit;
  p = lgl->seen.top;
  top = lgl->seen.top = lgl->seen.start + old;
  while (p > top) {
    lit = *--p;
    av = lglavar (lgl, lit);
    assert (av->mark);
    av->mark = 0;
    poisoned = av->poisoned;
    if (poisoned) continue;
    rsn = lglrsn (lgl, lit);
    r0 = rsn[0];
    tag = (r0 & MASKCS);
    assert (tag != DECISION);
    r1 = rsn[1];
    if (tag == BINCS || tag == TRNCS) {
      other = r0 >> RMSHFT;
      bv = lglavar (lgl, other);
      if (bv->poisoned) poisoned = 1;
      else if (tag == TRNCS) {
	bv = lglavar (lgl, r1);
	if (bv->poisoned) poisoned = 1;
      }
    } else {
      assert (tag == LRGCS);
      q = lglidx2lits (lgl, (r0 & REDCS), r1);
      while (!poisoned && (other = *q++))
	poisoned = lglavar (lgl, other)->poisoned;
    }
    if (!poisoned) continue;
    assert (!av->poisoned);
    av->poisoned = 1;
    lglpushstk (lgl, &lgl->poisoned, lit);
  }
  return 0;
}

static double lglpcnt (double n, double d) {
  return d != 0 ? 100.0 * n / d : 0.0;
}

static int lglrem (LGL * lgl) {
  int res = lgl->nvars;
  if (!res) return 0;
  assert (res >= 2);
  res -= lgl->stats.fixed.current + 2;
  assert (res >= 0);
  return res;
}

double lglprocesstime (void) {
  struct rusage u;
  double res;
  if (getrusage (RUSAGE_SELF, &u)) return 0;
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  return res;
}

double lglsec (LGL * lgl) {
  double time, delta;
  ABORTIF (!lgl, "uninitialized manager");
  time = lgl->getime ();
  delta = time - lgl->stats.time.entered.process;
  int i;
  if (delta < 0) delta = 0;
  lgl->stats.time.all += delta;
  lgl->stats.time.entered.process = time;
  for (i = 0; i < lgl->stats.time.entered.nesting; i++) {
    delta = time - lgl->stats.time.entered.phase[i];
    if (delta < 0) delta = 0;
    assert (lgl->stats.time.entered.ptr[i]);
    *lgl->stats.time.entered.ptr[i] += delta;
    lgl->stats.time.entered.phase[i] = time;
  }
  return lgl->stats.time.all;
}

static void lglstart (LGL * lgl, double * timestatsptr) {
  int nesting = lgl->stats.time.entered.nesting;
  assert (timestatsptr);
  assert (nesting < MAXPHN);
  lgl->stats.time.entered.ptr[nesting] = timestatsptr;
  lgl->stats.time.entered.phase[nesting] = lgl->getime ();
  lgl->stats.time.entered.nesting++;
}

static void lglstop (LGL * lgl) {
  double time = lgl->getime (), delta;
  int nesting = --lgl->stats.time.entered.nesting;
  assert (nesting >= 0);
  delta = time - lgl->stats.time.entered.phase[nesting];
  if (delta < 0) delta = 0;
  assert (lgl->stats.time.entered.ptr[nesting]);
  *lgl->stats.time.entered.ptr[nesting] += delta;
}

double lglmaxmb (LGL * lgl) {
  ABORTIF (!lgl, "uninitialized manager");
  return (lgl->stats.bytes.max + sizeof *lgl) / (double)(1<<20);
}

double lglmb (LGL * lgl) {
  ABORTIF (!lgl, "uninitialized manager");
  return (lgl->stats.bytes.current + sizeof *lgl) / (double)(1<<20);
}

static double lglagility (LGL * lgl) { return lgl->flips/1e5; }

static double lglavg (double n, double d) {
  return d != 0 ? n / d : 0.0;
}

static double lglheight (LGL * lgl) {
  return lglavg (lgl->stats.height, lgl->stats.decisions);
}

static void lglrephead (LGL * lgl) {
  if (lgl->tid > 0) return;
  assert (lgl->opts.verbose.val >= 1);
  if (lgl->msglock.lock) lgl->msglock.lock (lgl->msglock.state);
  printf ("c\n");
  printf ("c %s"
" seconds         irredundant          redundant clauses  agility"
"  height\n", !lgl->tid ? "  " : "");
  printf ("c %s"
"         variables clauses conflicts large binary ternary    hits"
"        MB\n", !lgl->tid ? "  " : "");
  printf ("c\n");
  fflush (stdout);
  if (lgl->msglock.unlock) lgl->msglock.unlock (lgl->msglock.state);
}

static void lglrep (LGL * lgl, int level, char type) {
  if (lgl->opts.verbose.val < level) return;
  if (!(lgl->stats.reported % REPMOD)) lglrephead (lgl);
  lglprt (lgl, 1,
             "%c %6.1f %7d %8d %9lld %7d %6d %5d %3.0f %3.0f %5.1f %4.0f",
	     type,
	     lglsec (lgl),
	     lglrem (lgl),
	     lgl->stats.irr,
	     (long long) lgl->stats.confs,
	     lgl->stats.red.lrg,
	     lgl->stats.red.bin,
	     lgl->stats.red.trn,
	     lglagility (lgl),
	     lglpcnt (lgl->stats.ronflicts, lgl->stats.rdded),
	     lglheight (lgl),
	     lglmb (lgl));
  lgl->stats.reported++;
}

static void lglflshrep (LGL * lgl) {
  if (!lgl->stats.reported) return;
  if (lgl->stats.reported % REPMOD) lglrephead (lgl);
  else lglprt (lgl, 1, "");
}

static void lglfitlir (LGL * lgl, Lir * lir) {
  lglfitstk (lgl, &lir->lits);
}

static void lglchkred (LGL * lgl) {
#ifndef NDEBUG
  int glue, idx, thisum, sum = 0, * p, * c;
  Lir * lir;
  for (glue = 0; glue < MAXGLUE; glue++) {
    lir = lgl->red + glue;
    thisum = 0;
    for (c = lir->lits.start; c < lir->lits.top; c = p + 1) {
      p = c;
      if (*p >= NOTALIT) continue;
      idx = (c - lir->lits.start) / 5;
      while (*p) p++;
      assert (p - c >= 4);
      thisum++;
    }
    assert (thisum == lgl->stats.lir[glue].clauses);
    sum += thisum;
  }
  assert (sum == lgl->stats.red.lrg);
#endif
}

static int lglcmpagsl (ASL * a, ASL * b) {
  int res;
  if ((res = (a->act - b->act))) return res;
  if ((res = ((b->lidx & GLUEMASK) - (a->lidx & GLUEMASK)))) return res;
  if ((res = (b->size - a->size))) return res;
  return a->lidx - b->lidx;
}

static int lglcmpasgl (ASL * a, ASL * b) {
  int res;
  if ((res = (a->act - b->act))) return res;
  if ((res = (b->size - a->size))) return res;
  if ((res = ((b->lidx & GLUEMASK) - (a->lidx & GLUEMASK)))) return res;
  return a->lidx - b->lidx;
}

#define NDVL 2 // should stay 1

static int lglneedacts (LGL * lgl, int * glueuselessptr) {
  int64_t clauses = 0, weighted = 0, tmp, avg, var = 0, std, delta;
  int glue;
  for (glue = 0; glue <= MAXGLUE; glue++) {
    tmp = lgl->stats.lir[glue].clauses;
    clauses += tmp;
    weighted += glue * tmp;
  }
  avg = clauses ? (10*weighted)/clauses : 0;
  lglprt (lgl, NDVL,
          "[needacts-%d] existing clauses glue average %.1f",
	  lgl->stats.reduced, avg/10.0);
  for (glue = 0; glue <= MAXGLUE; glue++) {
    delta = (10*glue - avg);
    var += delta*delta * lgl->stats.lir[glue].clauses;
  }
  var = clauses ? var / clauses : 0;
  std = lglceilsqrt64 (var);
  lglprt (lgl, NDVL,
          "[needacts-%d] existing clauses glue standard deviation %.1f",
	  lgl->stats.reduced, std/10.0);
  *glueuselessptr = (std < 10);
  if (avg > lgl->opts.actavgmax.val) return 1;
  if (std <= lgl->opts.actstdmin.val) return 1;
  if (std > lgl->opts.actstdmax.val) return 1;
  return 0;
}

static int lglagile (LGL * lgl) {
  return lgl->flips >= lgl->opts.agile.val * 100000;
}

static void lglreduce (LGL * lgl) {
  int * p, * q, * start, * c, ** maps, * sizes, * map, * eow, * rsn;
  int nlocked, collected, sumcollected, nunlocked, moved, act;
  int glue, minredglue, maxredglue, target, rem, nkeep;
  ASL * asls, * asl; int nasls, szasls;
  int inc, ifactor, acts, glueuseless;
  int size, idx, tag, red, i, blit;
  int r0, lidx, src, dst, lit;
  int64_t factor, hits;
  HTS * hts;
  AVar * av;
  DVar * dv;
  Lir * lir;
  lglchkred (lgl);
  lglstart (lgl, &lgl->stats.tms.red);
  lgl->stats.reduced.count++;
  LOG (1, "starting reduction %d", lgl->stats.reduced.count);
  rem = target = lgl->stats.red.lrg/2;
  LOG (2, "target is to collect %d clauses out of %d",
       target, lgl->stats.red.lrg);
  for (maxredglue = MAXGLUE-1; maxredglue >= 0; maxredglue--)
    if (lgl->stats.lir[maxredglue].clauses > 0) break;
  LOG (2, "maximum reduction glue %d", maxredglue);
  acts = lglneedacts (lgl, &glueuseless);
  if (lgl->opts.acts.val < 2) acts = lgl->opts.acts.val;
  if (acts) {
    lgl->stats.acts++;
    lglprt (lgl, NDVL,
            "[needacts-%d] using primarily activities for reduction",
	    lgl->stats.reduced);
    szasls = lgl->stats.red.lrg;
    minredglue = 0;
  } else {
    lglprt (lgl, NDVL,
            "[needacts-%d] using primarily glues for reduction",
            lgl->stats.reduced);
    asls = 0;
    if (maxredglue > 0) {
      for (minredglue = maxredglue;  minredglue > 0;  minredglue--) {
	lir = lgl->red + minredglue;
	LOG (2, "%d candidate clauses with glue %d",
	     lgl->stats.lir[minredglue].clauses, minredglue);
	if (lgl->stats.lir[minredglue].clauses >= rem) break;
	rem -= lgl->stats.lir[minredglue].clauses;
      }
    } else minredglue = 0;
    szasls = lgl->stats.lir[minredglue].clauses;
  }
  LOG (2, "minum reduction glue %d with %d remaining target clauses %.0f%%",
       minredglue, rem, lglpcnt (rem, target));
  NEW (maps, maxredglue + 1);
  NEW (sizes, maxredglue + 1);
  for (glue = minredglue; glue <= maxredglue; glue++) {
    lir = lgl->red + glue;
    size = lglcntstk (&lir->lits);
    assert (!size || size >= 6);
    size = (size + 5)/6;
    sizes[glue] = size;
    lglfitstk (lgl, &lir->lits);
    NEW (maps[glue], size);
    map = maps[glue];
    for (i = 0; i < size; i++) map[i] = -2;
  }
  nlocked = 0;
  for (i = 0; i < lglcntstk (&lgl->trail); i++) {
    lit = lglpeek (&lgl->trail, i);
    idx = abs (lit);
    av = lglavar (lgl, idx);
    rsn = lglrsn (lgl, idx);
    r0 = rsn[0];
    red = r0 & REDCS;
    if (!red) continue;
    tag = r0 & MASKCS;
    if (tag != LRGCS) continue;
    lidx = rsn[1];
    glue = lidx & GLUEMASK;
    if (glue == MAXGLUE) continue;
    if (glue < minredglue) continue;
    if (glue > maxredglue) continue;
    lir = lgl->red + glue;
    lidx >>= GLUESHFT;
    LOGCLS (5, lir->lits.start + lidx,
            "locking reason of literal %d glue %d clause",
	    lit, glue);
    lidx /= 6;
    assert (lidx < sizes[glue]);
    assert (maps[glue][lidx] == -2);
    maps[glue][lidx] = -1;
    nlocked++;
  }
  LOG (2, "locked %d learned clauses %.0f%%",
       nlocked, lglpcnt (nlocked, lgl->stats.red.lrg));
  NEW (asls, szasls);
  nasls = 0;
  for (glue = minredglue; glue <= maxredglue; glue++) {
    lir = lgl->red + glue;
    start = lir->lits.start;
    for (c = start; c < lir->lits.top; c = p + 1) {
      act = *c;
      if (act == REMOVED) {
	for (p = c + 1; p < lir->lits.top && *p == REMOVED; p++)
	  ;
	p--;
	continue;
      }
      for (p = ++c; *p; p++)
	;
      assert (nasls < szasls);
      asl = asls + nasls++;
      asl->act = act;
      asl->size = p - c;
      asl->lidx = ((c - start) << GLUESHFT) | glue;
    }
    if (!acts) { assert (glue == minredglue); break; }
  }
  assert (nasls == szasls);
  if (glueuseless) SORT (asls, nasls, lglcmpasgl);
  else SORT (asls, nasls, lglcmpagsl);
  LOG (1, "copied and sorted %d activities", nasls);
  nkeep = 0;
  for (idx = rem; idx < nasls; idx++) {
    asl = asls + idx;
    lidx = asl->lidx;
    glue = lidx & GLUEMASK;
    lidx >>= GLUESHFT;
    lidx /= 6;
    assert (lidx < sizes[glue]);
    maps[glue][lidx] = -1;
    nkeep++;
  }
  DEL (asls, szasls);
  LOG (1, "explicity marked %d additional clauses to keep", nkeep);
  sumcollected = 0;
  for (glue = minredglue; glue <= maxredglue; glue++) {
    lir = lgl->red + glue;
    map = maps[glue];
    size = sizes[glue];
    q = start = lir->lits.start;
    collected = 0;
    for (c = start; c < lir->lits.top; c = p + 1) {
      act = *c++;
      if (act == REMOVED) {
	for (p = c; p < lir->lits.top && *p == REMOVED; p++)
	  ;
	assert (p >= lir->lits.top || *p < NOTALIT || lglisact (*p));
	p--;
	continue;
      }
      p = c;
      lglchkact (act);
      src = (c - start)/6;
      assert (src < size);
      if (map[src] == -2) {
	assert (collected < lgl->stats.lir[glue].clauses);
	collected++;
	LOGCLS (5, c, "collecting glue %d clause", glue);
	while (*p) p++;
      } else {
	dst = q - start + 1;
	map[src] = dst;
	if (p == q) {
	  while (*p) p++;
	  q = p + 1;
	} else {
	  *q++ = act;
	  LOGCLS (5, c, "moving from %d to %d glue %d clause",
	          (c - start), dst, glue);
	  while (*p) *q++ = *p++;
	  *q++ = 0;
	}
      }
    }
    LOG (2, "collected %d glue %d clauses", collected, glue);
    sumcollected += collected;
    assert (sumcollected <= lgl->stats.red.lrg);
    assert (lgl->stats.lir[glue].clauses >= collected);
    lgl->stats.lir[glue].clauses -= collected;
    lgl->stats.lir[glue].reduced += collected;
    lir->lits.top = q;
    lglfitlir  (lgl, lir);
  }
  LOG (2, "collected altogether %d clauses", sumcollected);
  assert (sumcollected <= lgl->stats.red.lrg);
  lgl->stats.red.lrg -= sumcollected;
  nunlocked = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    if (!lglval (lgl, idx)) continue;
    av = lglavar (lgl, idx);
    rsn = lglrsn (lgl, idx);
    r0 = rsn[0];
    red = r0 & REDCS;
    if (!red) continue;
    tag = r0 & MASKCS;
    if (tag != LRGCS) continue;
    lidx = rsn[1];
    glue = lidx & GLUEMASK;
    if (glue < minredglue) continue;
    if (glue > maxredglue) continue;
    lir = lgl->red + glue;
    src = (lidx >> GLUESHFT);
    assert (src/6 < sizes[glue]);
    dst = maps[glue][src/6];
    assert (dst >= 0);
    dst <<= GLUESHFT;
    dst |= lidx & GLUEMASK;
    rsn[1] = dst;
    nunlocked++;
  }
  LOG (2, "unlocked %d reasons", nunlocked);
  assert (nlocked == nunlocked);
  collected = moved = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    dv = lgldvar (lgl, idx);
    for (i = 0; i <= 1; i++) {
      hts = dv->hts + i;
      if (!hts->offset) continue;
      q = lglhts2wchs (lgl, hts);
      assert (hts->count >= 0);
      eow = q + hts->count;
      for (p = q; p < eow; p++) {
	blit = *p;
	red = blit & REDCS;
	tag = blit & MASKCS;
	if (red && tag == LRGCS) {
	  lidx = *++p;
	  glue = lidx & GLUEMASK;
	  if (glue < minredglue || glue > maxredglue) {
	    dst = lidx >> GLUESHFT;
	  } else {
	    lir = lgl->red + glue;
	    src = lidx >> GLUESHFT;
	    assert (src/6 < sizes[glue]);
	    dst = maps[glue][src/6];
	  }
	  if (dst >= 0) {
	    moved++;
	    *q++ = blit;
	    *q++ = (dst << GLUESHFT) | (lidx & GLUEMASK);
	  } else collected++;
	} else {
	  *q++ = blit;
	  if (tag != BINCS) {
	    assert (tag == TRNCS || tag == LRGCS);
	    *q++ = *++p;
	  }
	}
      }
      lglshrinkhts (lgl, hts, hts->count - (p - q));
    }
  }
  LOG (1, "moved %d and collected %d occurrences", moved, collected);
  for (glue = minredglue; glue <= maxredglue; glue++) {
    lir = lgl->red + glue;
    DEL (maps[glue], sizes[glue]);
  }
  DEL (sizes, maxredglue+1);
  DEL (maps, maxredglue+1);
  hits = 100ll * lgl->stats.ronflicts;
  hits /= 1 + lgl->stats.rdded;
  if (hits < lgl->opts.redlexpinc.val) {
    factor = 5*hits;
    ifactor = (factor < (int64_t) INT_MAX) ? factor : INT_MAX;
    if (ifactor > lgl->opts.redlmaxinc.val) factor = lgl->opts.redlmaxinc.val;
    if (ifactor < lgl->opts.redlmininc.val) factor = lgl->opts.redlmininc.val;
    inc = (ifactor * lgl->opts.redlinc.val + 99) / 100;
    LOG (1, "reduce factor %.2f", ifactor/100.0);
    lglprt (lgl, 1, "arithmetic increase of reduce limit");
    lgl->stats.reduced.arith++;
  } else {
    inc = (lgl->opts.redlexpfac.val * lgl->limits.reduce + 99)/100;
    if (!inc) inc++;
    lglprt (lgl, 1, "exponential increase of reduce limit");
    lgl->stats.reduced.geom++;
  }
  LOG (1, "reduce increment %d", inc);
  lgl->limits.reduce += inc;
  LOG (1, "new reduce limit of %d redundant clauses", lgl->limits.reduce);
  lglrep (lgl, 1, '+');
  lgl->stats.ronflicts /= 2;
  lgl->stats.rdded /= 2;
  lglchkred (lgl);
  lglstop (lgl);
}

static void lglrmbwch (LGL * lgl, int lit, int other, int red) {
  int * p, blit, blit1, * w, * eow, tag;
  HTS * hts;
  assert (!red || red == REDCS);
  LOG (3, "removing %s binary watch %d blit %d",
       lglred2str (red), lit, other);
  hts = lglhts (lgl, lit);
  assert (hts->count >= 1);
  p = w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  blit1 = (other << RMSHFT) | red | BINCS;
  for (;;) {
    assert (p < eow);
    if (p == eow) return;	//TODO remove this
    blit = *p++;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) { p++; continue; }
    if (tag == IRRCS) { assert (lgl->dense); continue; }
    assert (tag == BINCS);
    if (blit == blit1) break;
  }
  while (p < eow) p[-1] = p[0], p++;
  lglshrinkhts (lgl, hts, p - w - 1);
}

static int lglpopesched (LGL * lgl) {
  Stk * s = &lgl->esched;
  int res, last, cnt, * p;
  EVar * ev;
  assert (!lglmtstk (s));
  res = *s->start;
  assert (!lglifrozen (lgl, res));
  LOGESCHED (4, res, "popped");
  ev = lglevar (lgl, res);
  assert (!ev->pos);
  ev->pos = -1;
  last = lglpopstk (s);
  cnt = lglcntstk (s);
  if (!cnt) { assert (last == res); return res; }
  p = lglepos (lgl, last);
  assert (*p == cnt);
  *p = 0;
  *s->start = last;
  lgledown (lgl, last);
  return res;
}

static void lgldecocc (LGL * lgl, int lit) {
  int idx = abs (lit), old, sign = (lit < 0);
  EVar * ev = lglevar (lgl, lit);
  if (!lglisfree (lgl, lit)) return;
  assert (ev->occ[sign] > 0);
  ev->occ[sign] -= 1;
  old = lglecalc (lgl, ev);
  assert (ev->score <= old);
  LOG (3, "dec occ of %d gives escore[%d] = %d with occs %d %d",
       lit, idx, ev->score, ev->occ[0], ev->occ[1], ev->score);
  if (ev->pos < 0) {
    if (lgl->elm.pivot != idx) lglesched (lgl, idx);
  } else if (old > ev->score) lgleup (lgl, idx);
}

static void lglrmbcls (LGL * lgl, int a, int b, int red) {
  lglrmbwch (lgl, a, b, red);
  lglrmbwch (lgl, b, a, red);
  LOG (2, "removed %s binary clause %d %d", lglred2str (red), a, b);
  lgldeclscnt (lgl, 2, red, 0);
  if (!red && lgl->dense) lgldecocc (lgl, a), lgldecocc (lgl, b);
}

static void lglrmtcls (LGL * lgl, int a, int b, int c, int red) {
  lglrmtwch (lgl, a, b, c, red);
  lglrmtwch (lgl, b, a, c, red);
  lglrmtwch (lgl, c, a, b, red);
  LOG (2, "removed %s ternary clause %d %d %d", lglred2str (red), a, b, c);
  lgldeclscnt (lgl, 3, red, 0);
  if (!red && lgl->dense)
    lgldecocc (lgl, a), lgldecocc (lgl, b), lgldecocc (lgl, c);
}

static void lglrmlocc (LGL * lgl, int lit, int lidx) {
  int search, blit, tag, * p, * q, * w, * eow;
  HTS * hts;
#ifndef NLGLOG
  LOG (3, "removing occurrence %d in irr[%d]", lit, lidx);
#endif
  hts = lglhts (lgl, lit);
  assert (hts->count >= 1);
  assert (lidx <= MAXIRRLIDX);
  search = (lidx << RMSHFT) | IRRCS;
  assert (search >= 0);
  p = w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  do {
    assert (p < eow);
    blit = *p++;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
  } while (blit != search);
  assert (p[-1] == search);
  for (q = p ; q < eow; q++)
    q[-1] =q[0];
  lglshrinkhts (lgl, hts, q - w - 1);
}

static void lglrmlcls (LGL * lgl, int lidx, int red) {
  int * c, * p, glue, lit;
  glue = red ? (lidx & GLUEMASK) : 0;
  c = lglidx2lits (lgl, red, lidx);
  if ((red && glue != MAXGLUE) || (!red && !lgl->dense)) {
    lglrmlwch (lgl, c[0], red, lidx);
    lglrmlwch (lgl, c[1], red, lidx);
  }
  if (!red && lgl->dense) {
    for (p = c; (lit = *p); p++) {
      lglrmlocc (lgl, lit, lidx);
      lgldecocc (lgl, lit);
    }
  }
  if (red && glue < MAXGLUE) { lglchkact (c[-1]); c[-1] = REMOVED; }
  for (p = c; *p; p++) *p = REMOVED;
  *p = REMOVED;
  if (glue != MAXGLUE) lgldeclscnt (lgl, 4, red, glue);
}

static void lgldynsub (LGL * lgl, int lit, int r0, int r1) {
  int red, tag;
  tag = r0 & MASKCS;
  LOGREASON (2, lit, r0, r1, "removing subsumed");
  red = r0 & REDCS;
  if (red) lgl->stats.otfs.sub.dyn.red++;
  else lgl->stats.otfs.sub.dyn.irr++;
  if (tag == BINCS) lglrmbcls (lgl, lit, (r0>>RMSHFT), red);
  else if (tag == TRNCS) lglrmtcls (lgl, lit, (r0>>RMSHFT), r1, red);
  else { assert (tag == LRGCS); lglrmlcls (lgl, r1, red); }
}

static void lglunflict (LGL * lgl, int lit) {
  lgl->conf.lit = lit;
  lgl->conf.rsn[0] = (lit << RMSHFT) | UNITCS;
  LOG (2, "inconsistent unary clause %d", lit);
}

static void lgldynstr (LGL * lgl, int del, int lit, int r0, int r1) {
  int * p, * c, lidx, other, red, tag, glue, other2, other3, pos, blit;
  tag = r0 & MASKCS;
  LOGREASON (2, lit, r0, r1, "strengthening by removing %d from", del);
  red = r0 & REDCS;
  if (red) lgl->stats.otfs.str.dyn.red++;
  else lgl->stats.otfs.str.dyn.irr++;
  if (tag == BINCS) {
    other = (del == lit) ? (r0 >> RMSHFT) : lit;
    assert (other != del);
    lglrmbcls (lgl, del, other, red);
#ifndef NLGLPICOSAT
    lglpicosatchkclsarg (lgl, other, 0);
#endif
    lglunflict (lgl, other);
    return;
  }
  if (tag == TRNCS) {
    if (lit == del) other = (r0 >> RMSHFT), other2 = r1;
    else if (del == r1) other = lit, other2 = (r0 >> RMSHFT);
    else other = lit, other2 = r1;
    assert (del != other && del != other2);
    lglrmtcls (lgl, del, other, other2, red);
#ifndef NLGLPICOSAT
    lglpicosatchkclsarg (lgl, other, other2, 0);
#endif
    if (!red) lgl->stats.irr++, assert (lgl->stats.irr > 0);
    else lgl->stats.red.bin++, assert (lgl->stats.red.bin > 0);
    lglwchbin (lgl, other, other2, red);
    lglwchbin (lgl, other2, other, red);
    if (lglevel (lgl, other) < lglevel (lgl, other2)) SWAP (other, other2);
    blit = (other2 << RMSHFT) | BINCS | red;
    lglbonflict (lgl, other, blit);
    return;
  }
  assert (tag == LRGCS);
  lidx = r1;
  glue = red ? (lidx & GLUEMASK) : 0;
  c = lglidx2lits (lgl, red, lidx);
  for (p = c; *p != del; p++)
    assert (*p);
  pos = p - c;
  if (pos <= 1 && glue != MAXGLUE) {
    lglrmlwch (lgl, c[0], red, lidx);
    lglrmlwch (lgl, c[1], red, lidx);
  }
  while ((other = *++p)) p[-1] = other;
  p[-1] = 0, *p = REMOVED;
  lglorderclsaux (lgl, c + 0);
  lglorderclsaux (lgl, c + 1);
#ifndef NLGLPICOSAT
  lglpicosatchkclsaux (lgl, c);
#endif
  assert (p - c > 3);
  if (p - c == 4) {
    assert (glue != MAXGLUE && !c[3] && c[4] >= NOTALIT);
    other = c[0], other2 = c[1], other3 = c[2];
    if (pos > 1 && glue != MAXGLUE) {
      lglrmlwch (lgl, c[0], red, lidx);
      lglrmlwch (lgl, c[1], red, lidx);
    }
    if (red && glue < MAXGLUE) { lglchkact (c[-1]); c[-1] = REMOVED; }
    c[0] = c[1] = c[2] = c[3] = REMOVED;
    if (lglevel (lgl, other2) < lglevel (lgl, other3)) SWAP (other2, other3);
    if (lglevel (lgl, other) < lglevel (lgl, other2)) SWAP (other, other2);
    lglwchtrn (lgl, other, other2, other3, red);
    lglwchtrn (lgl, other2, other, other3, red);
    lglwchtrn (lgl, other3, other, other2, red);
    if (red) {
      assert (lgl->stats.red.lrg > 0);
      lgl->stats.red.lrg--;
      assert (lgl->stats.lir[glue].clauses > 0);
      lgl->stats.lir[glue].clauses--;
      lgl->stats.red.trn++;
      assert (lgl->stats.red.trn > 0);
    }
    lgltonflict (lgl, other, (other2 << RMSHFT) | red | TRNCS, other3);
  } else {
    if (pos <= 1 && glue != MAXGLUE) {
      LOG (3, "new head literal %d", c[0]);
      (void) lglwchlrg (lgl, c[0], c[1], red, lidx);
      LOG (3, "new tail literal %d", c[1]);
      (void) lglwchlrg (lgl, c[1], c[0], red, lidx);
    }
    lglonflict (lgl, 0, c[0], red, lidx);
  }
  lgl->stats.prgss++;
}

static void lglpopnunmarkstk (LGL * lgl, Stk * stk) {
  while (!lglmtstk (stk))
    lglavar (lgl, lglpopstk (stk))->mark = 0;
}

static void lglclnframes (LGL * lgl) {
  while (!lglmtstk (&lgl->frames))
    lglunuselevel (lgl, lglpopstk (&lgl->frames));
}

static void lglclnpoisoned (LGL * lgl) {
  AVar * av;
  int lit;
  while (!lglmtstk (&lgl->poisoned)) {
    lit = lglpopstk (&lgl->poisoned);
    av = lglavar (lgl, lit);
    assert (!av->mark);
    assert (av->poisoned);
    av->poisoned = 0;
  }
}

static int lglavglen (LGL * lgl) {
  int64_t clauses = lgl->stats.clauses.learned;
  int64_t lits = lgl->stats.lits.learned;
  int64_t res64 = (lits + clauses + 1) / (clauses + 1);
  int res32;
  assert (1 <= res64 && res64 <= INT_MAX);
  res32 = res64;
  return res32;
}

static int lglstr (LGL * lgl) {
  if (!lgl->opts.elim.val) return 1;
  if (lgl->stats.elm.count < lgl->opts.elmnostr.val) return 0;
  if (lgl->stats.elm.count > lgl->opts.elmnostr.val) return 1;
  if (lgl->eliminating) return 0;
  return 1;
}

static int lglana (LGL * lgl) {
  int size, savedsize, resolventsize, level, mlevel, jlevel, red, glue;
  int open, resolved, tag, lit, uip, r0, r1, other, * p, * q;
  int minlim, minimized, len, * rsn;
  int rescore_clauses, rescore_vars;
  int del, cl, c0, c1, sl, s0, s1;
  int64_t tmp;
  AVar * av;
  if (lgl->mt) return 0;
  if (lgl->failed) return 0;
  if (!lgl->conf.lit) return 1;
  if (!lgl->level) {
#ifndef NLGLPICOSAT
    lglpicosatchkcls (lgl);
#endif
    lgl->mt = 1;
    return 0;
  }
  lglstart (lgl, &lgl->stats.tms.ana);
  lgl->stats.confs++;
  assert (lgl->conf.lit);
  assert (lglmtstk (&lgl->seen));
  assert (lglmtstk (&lgl->clause));
  assert (lglmtstk (&lgl->resolvent));
#ifndef NDEBUG
  if (lgl->opts.check.val > 0) lglchkclnvar (lgl);
#endif
  open = 0;
  lit = lgl->conf.lit, r0 = lgl->conf.rsn[0], r1 = lgl->conf.rsn[1];
RESTART:
  rescore_clauses = rescore_vars = 0;
  uip = savedsize = resolved = 0;
  open += lglpull (lgl, lit, &rescore_vars);
  LOG (2, "starting analysis with reason of literal %d", lit);
  for (;;) {
    LOGREASON (2, lit, r0, r1, "analyzing");
    if (resolved++) {
#ifdef RESOLVENT
      if (lglmaintainresolvent (lgl)) {
	LOG (2, "removing %d from resolvent", -lit);
	lglrmstk (&lgl->resolvent, -lit);
	LOGRESOLVENT (3, "resolvent after removing %d is", -lit);
      }
#endif
    }
    assert (lglevel (lgl, lit) == lgl->level);
    tag = r0 & MASKCS;
    if (tag == BINCS || tag == TRNCS) {
      other = r0 >> RMSHFT;
      size = lglevel (lgl, other) ? 2 : 1;
      if (lglpull (lgl, other, &rescore_vars)) open++;
      if (tag == TRNCS) {
	if (lglevel (lgl, r1)) size++;
        if (lglpull (lgl, r1, &rescore_vars)) open++;
      }
    } else {
      assert (tag == LRGCS);
      red = r0 & REDCS;
      p = lglidx2lits (lgl, red, r1);
      size = 0;
      while ((other = *p++)) {
	if (lglevel (lgl, other)) size++;
	if (lglpull (lgl, other, &rescore_vars)) open++;
      }
      if (red && lglbumplidx (lgl, r1)) rescore_clauses = 1;
    }
    LOG (3, "open %d antecendents %d learned %d resolved %d",
         open-1, size, lglcntstk (&lgl->clause), lglcntstk (&lgl->resolvent));
    assert (open > 0);
    resolventsize = open + lglcntstk (&lgl->clause);
#ifdef RESOLVENT
    LOGRESOLVENT (2, "resolvent");
    if (lglmaintainresolvent (lgl))
      assert (lglcntstk (&lgl->resolvent) == resolventsize);
#endif
    if (lglstr (lgl) &&
        lgl->opts.otfs.val &&
        (resolved >= 2) &&
        (resolventsize<size || (resolved==2 && resolventsize<savedsize))) {
      cl = lgl->conf.lit;
      c0 = lgl->conf.rsn[0];
      c1 = lgl->conf.rsn[1];
      assert (resolved >= 2);
      del = lit;
      if (resolved > 2) ;
      else if (resolventsize >= size) del = -lit, lit = cl, r0 = c0, r1 = c1;
      else if (resolventsize >= savedsize) ;
      else {
	if (r0 & REDCS) {
	  sl = lit, s0 = r0, s1 = r1;
	  del = -lit, lit = cl, r0 = c0, r1 = c1;
	} else sl = cl, s0 = c0, s1 = c1;
	lgldynsub (lgl, sl, s0, s1);
      }
      lgldynstr (lgl, del, lit, r0, r1);
      lit = lgl->conf.lit;
      r0 = lgl->conf.rsn[0];
      r1 = lgl->conf.rsn[1];
      assert (lglevel (lgl, lit) == lgl->level);
      jlevel = 0;
      tag = r0 & MASKCS;
      if (tag == UNITCS) ;
      else if (tag == BINCS) {
	other = r0 >> RMSHFT;
	level = lglevel (lgl, other);
	if (level > jlevel) jlevel = level;
      } else if (tag== TRNCS) {
	other = r0 >> RMSHFT;
	level = lglevel (lgl, other);
	if (level > jlevel) jlevel = level;
	if (jlevel < lgl->level) {
	  other = r1;
	  level = lglevel (lgl, other);
	  if (level > jlevel) jlevel = level;
	}
      } else {
	assert (tag == LRGCS);
	red = r0 & REDCS;
	p = lglidx2lits (lgl, red, r1);
	while (jlevel < lgl->level && (other = *p++)) {
	  level = lglevel (lgl, other);
	  if (level > jlevel) jlevel = level;
	}
	if (red && lglbumplidx (lgl, r1)) rescore_clauses = 1;
      }
      if (jlevel >= lgl->level) {
	LOG (2, "restarting analysis after on-the-fy strengthening");
	if (rescore_vars) lglrescorevars (lgl);
	if (rescore_clauses) lglrescoreclauses (lgl);
	goto RESTART;
      }
      LOGREASON (2, lit, r0, r1,
		 "driving %d at level %d through strengthened",
		 lit, jlevel);
      lgl->stats.otfs.driving++;
      if (lglbumplit (lgl, lit)) rescore_vars = 1;
      lglbacktrack (lgl, jlevel);
      lglassign (lgl, lit, r0, r1);
      goto DONE;
    }
    savedsize = size;
    while (!lglmarked (lgl, lit = lglpopstk (&lgl->trail)))
      lglunassign (lgl, lit);
    lglunassign (lgl, lit);
    if (!--open) { uip = -lit; break; }
    LOG (2, "analyzing reason of literal %d next", lit);
    av = lglavar (lgl, lit);
    rsn = lglrsn (lgl, lit);
    r0 = rsn[0], r1 = rsn[1];
  }
  assert (uip);
  LOG (2, "adding UIP %d at same level %d to 1st UIP clause",
       uip, lgl->level);
  lglpushstk (lgl, &lgl->clause, uip);
  assert (lglmarked (lgl, uip));
#ifdef RESOLVENT
  LOGRESOLVENT (3, "final resolvent before flushing fixed literals");
  if (lglmaintainresolvent  (lgl)) {
    q = lgl->resolvent.start;
    for (p = q; p < lgl->resolvent.top; p++)
      if (lglevel (lgl, (other = *p)))
	*q++ = other;
    lgl->resolvent.top = q;
    LOGRESOLVENT (2, "final resolvent after flushing fixed literals");
    assert (lglcntstk (&lgl->resolvent) == lglcntstk (&lgl->clause));
    for (p = lgl->clause.start; p < lgl->clause.top; p++)
      assert (lglavar (lgl, *p)->mark == 1);
    for (p = lgl->resolvent.start; p < lgl->resolvent.top; p++) {
      av = lglavar (lgl, *p); assert (av->mark == 1); av->mark = 0;
    }
    for (p = lgl->clause.start; p < lgl->clause.top; p++)
      assert (lglavar (lgl, *p)->mark == 0);
    for (p = lgl->resolvent.start; p < lgl->resolvent.top; p++) {
      av = lglavar (lgl, *p); assert (av->mark == 0); av->mark = 1;
    }
    lglclnstk (&lgl->resolvent);
  }
#endif
  lglpushstk (lgl, &lgl->clause, 0);
  LOGCLS (2, lgl->clause.start, "1st UIP clause");
#ifndef NLGLPICOSAT
  lglpicosatchkcls (lgl);
#endif
  lgl->stats.lits.nonmin += lglcntstk (&lgl->clause) - 1;
  q = lgl->clause.start;
  tmp = lglcntstk (&lgl->clause) * (int64_t) lgl->opts.minlim.val;
  glue = lglcntstk (&lgl->frames);
  if (glue == 1) tmp *= 8;
  else if (glue == 2) tmp *= 4;
  else if (glue == 3) tmp *= 2;
  minlim = (tmp > (int64_t) INT_MAX) ? INT_MAX : (int) tmp;
  assert (0 <= minlim);
  minimized = 0;
  assert (lglmtstk (&lgl->poisoned));
  for (p = q; (other = *p); p++)
    if (other != uip && lglmincls (lgl, other, &minlim)) {
      minimized++;
      LOG (2, "removed %d", other);
    } else *q++ = other;
  *q++ = 0;
  lglclnpoisoned (lgl);
  assert (lgl->clause.top - q == minimized);
  LOG (2, "clause minimized by %d literals", minimized);
  LOGCLS (2, lgl->clause.start, "minimized clause");
  lgl->clause.top = q;
  mlevel = lgl->level, jlevel = 0, glue = 0;
  for (p = lgl->frames.start; p < lgl->frames.top; p++) {
    level = *p;
    assert (0 < level && level < lgl->level);
    if (level < mlevel) mlevel = level;
    if (level > jlevel) jlevel = level;
    glue++;
  }
  assert (glue == lglcntstk (&lgl->frames));
  LOG (2, "jump level %d", jlevel);
  LOG (2, "minimum level %d", mlevel);
  LOG (2, "glue %d covers %.0f%%", glue,
       (float)(jlevel ? lglpcnt (glue, (jlevel - mlevel) + 1) : 100.0));
  if (lglrsn (lgl, uip)[0]) lgl->stats.uips++;
  lglbacktrack (lgl, jlevel);
  len = lglcntstk (&lgl->clause) - 1;
  lgl->stats.clauses.glue += glue;
  lgl->stats.lits.learned += len;
  lgl->stats.clauses.learned++;
  if (glue > 2 &&
      lgl->opts.caplen.val &&
      (100*len)/lgl->opts.caplen.val > lglavglen (lgl)) {
    lgl->stats.clauses.capped++;
    glue = MAXGLUE;
  }
#ifndef NLGLPICOSAT
  lglpicosatchkcls (lgl);
#endif
  lgladdcls (lgl, REDCS, glue);
DONE:
#ifdef RESOLVENT
  if (lglmaintainresolvent  (lgl)) lglclnstk (&lgl->resolvent);
#endif
  lglclnstk (&lgl->clause);
  lglpopnunmarkstk (lgl, &lgl->seen);
  lglclnframes (lgl);
  if (lglbumpscinc (lgl)) rescore_vars = 1;
  if (!lgl->level) { lgl->stats.iterations++; lglrep (lgl, 1, 'i'); }
  if (rescore_clauses) lglrescoreclauses (lgl);
  if (rescore_vars) lglrescorevars (lgl);
  lglstop (lgl);
  return 1;
}

static int lgluby (int i) {
  int k;
  for (k = 1; k < 32; k++)
    if (i == (1 << k) - 1)
      return 1 << (k - 1);

  for (k = 1;; k++)
    if ((1 << (k - 1)) <= i && i < (1 << k) - 1)
      return lgluby (i - (1 << (k-1)) + 1);
}

static void lglincrestartl (LGL * lgl, int skip) {
  int delta = lgl->opts.restartint.val * lgluby (++lgl->limits.restart.luby);
  lgl->limits.restart.confs = lgl->stats.confs + delta;
  if (lgl->limits.restart.wasmaxdelta) {
    assert (!skip);	//so we will never see an 'N'
    lglrep (lgl, 1, skip ? 'N' : 'R');
  } else lglrep (lgl, 2, skip ? 'n' : 'r');
  if (delta > lgl->limits.restart.maxdelta) {
    lgl->limits.restart.wasmaxdelta = 1;
    lgl->limits.restart.maxdelta = delta;
  } else lgl->limits.restart.wasmaxdelta = 0;
}

static void lglincrebiasl (LGL * lgl, int skip) {
  int delta = lgl->opts.rebint.val * lgluby (++lgl->limits.rebias.luby);
  lgl->limits.rebias.confs = lgl->stats.confs + delta;
  if (lgl->limits.rebias.wasmaxdelta) {
    assert (!skip);	//so we will never see an 'O'
    lglrep (lgl, 1, skip ? 'O' : 'B');
  } else lglrep (lgl, 2, skip ? 'o' : 'b');
  if (delta > lgl->limits.rebias.maxdelta) {
    lgl->limits.rebias.wasmaxdelta = 1;
    lgl->limits.rebias.maxdelta = delta;
  } else lgl->limits.rebias.wasmaxdelta = 0;
}

static void lgldschedtrail (LGL * lgl) {
  const int * p;
  int lit;
  for (p = lgl->trail.start; p < lgl->trail.top; p++)
    if (!lgldscheduled (lgl, (lit = *p))) lgldsched (lgl, lit);
}

static int lglmatchtrail (LGL * lgl) {
  int res = 0, lit, size, i, level, * start;
  lgldschedtrail (lgl);
  start = lgl->dsched.start;
  i = size = lglcntstk (&lgl->dsched);
  while (!lglmtstk (&lgl->dsched)) {
    assert (i == lglcntstk (&lgl->dsched));
    lit = lglpopdsched (lgl);
    assert (start == lgl->dsched.start && (start + i <= lgl->dsched.end));
    start[--i] = lit;
    if (!lglval (lgl, lit)) break;
    if ((level = lglevel (lgl, lit)) <= res) continue;
    if (lgldecision (lgl, lit) && level == res + 1) res++;
    else break;
  }
  while (i < size) {
    assert (start == lgl->dsched.start && (start + i < lgl->dsched.end));
    lit = start[i++];
    if (!lglval (lgl, lit) || lglevel (lgl, lit) > res)
      lgldsched (lgl, lit);
  }
  if (res)
    lglprt (lgl, 2,
    "match trail level %d from current level %d", res, lgl->level);
  return res;
}

static int lglpermutetrail (LGL * lgl) {
  int res, lit, size, i, level, * start, min, count;
  lgldschedtrail (lgl);
  start = lgl->dsched.start;
  i = size = lglcntstk (&lgl->dsched);
  res = min = count = 0;
  while (!lglmtstk (&lgl->dsched)) {
    assert (i == lglcntstk (&lgl->dsched));
    lit = lglpopdsched (lgl);
    assert (start == lgl->dsched.start && (start + i <= lgl->dsched.end));
    start[--i] = lit;
    if (!lglval (lgl, lit)) break;
    if ((level = lglevel (lgl, lit)) > min) min = level;
    if (lgldecision (lgl, lit) && ++count == min) res = count;
  }
  while (i < size) {
    assert (start == lgl->dsched.start && (start + i < lgl->dsched.end));
    lit = start[i++];
    if (!lglval (lgl, lit) || lglevel (lgl, lit) > res)
      lgldsched (lgl, lit);
  }
  if (res)
    lglprt (lgl, 2,
    "permute trail level %d from current level %d", res, lgl->level);
  return res;
}

static int lglreusetrail (LGL * lgl) {
  int next = 0, res = 0, prev, level;
  const Ctr * p;
  while (!lglmtstk (&lgl->dsched)) { 
    next = lgltopdsched (lgl);
    if (!lglval (lgl, next)) break;
    lglpopdsched (lgl);
  }
  if (!next) return 0;
  for (p = lgl->control.start + 1; p < lgl->control.top; p++) {
    prev = p->decision;
    assert (lgldecision (lgl, prev));
    if (lgldcmp (lgl, prev, next) < 0) break;
    level = lglevel (lgl, prev);
    assert (level == p - lgl->control.start);
    assert (res + 1 == level);
    res = level;
  }
  if (res)
    lglprt (lgl, 2,
    "reuse trail level %d from current level %d", res, lgl->level);
  return res;
}

static void lglrestart (LGL * lgl) {
  int skip = lgl->limits.restart.wasmaxdelta ? 0 : lglagile (lgl), level;
  double kept;
  lglstart (lgl, &lgl->stats.tms.rsts);
  if (skip) {
    lgl->stats.restarts.skipped++;
    LOG (1, "skipping restart with agility %.0f%%", lglagility (lgl));
  } else {
    LOG (1, "restarting with agility %.0f%%", lglagility (lgl));
    switch (lgl->opts.restartype.val) {
      default: level = 0; break;
      case 1: level = lglmatchtrail (lgl); break;
      case 2: level = lglpermutetrail (lgl); break;
      case 3: level = lglreusetrail (lgl); break;
    }
    lglbacktrack (lgl, level);
    if (level) {
      assert (lgl->level > 0);
      kept = level / (double) lgl->level;
      lgl->stats.restarts.kept.sum += kept;
      lgl->stats.restarts.kept.count++;
    }
    lgl->stats.restarts.count++;
  }
  lglincrestartl (lgl, skip);
  lglstop (lgl);
}

static void lgldefrag (LGL * lgl) {
  int * p, * eow, * q, lit, idx, sign, move, recycled, ld, offset;
  int next, cnt, blit;
  HTS * hts;
  lglstart (lgl, &lgl->stats.tms.dfg);
  lgl->stats.defrags++;
  LOG (2, "recycling %d free watch stacks altogether", lgl->nfreewchs);
  for (ld = 0; ld < MAXLDFW; ld++) {
    cnt = 0;
    offset = lgl->freewchs[ld];
    if (offset != INT_MAX) {
      lgl->freewchs[ld] = INT_MAX;
      assert (lgl->nfreewchs > 0);
      lgl->nfreewchs--;
      cnt++;
      while ((next = lglpeek (&lgl->wchs, offset)) != INT_MAX) {
	lglpoke (&lgl->wchs, offset, INT_MAX);
	assert (lgl->nfreewchs > 0);
	lgl->nfreewchs--;
	LOG (3, "recycled watch stack at %d of size %d", offset, (1<<ld));
 	offset = next;
	cnt++;
      }
      if (cnt) LOG (3, "recycled %d watch stacks of size %d", cnt, (1<<ld));
    }
  }
  cnt = 0;
  assert (!lgl->nfreewchs);
  assert (lglmtstk (&lgl->saved));
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = idx * sign;
      hts = lglhts (lgl, lit);
      if (!hts->offset) continue;
      p = lglhts2wchs (lgl, hts);
      blit = *p;
      assert (abs (blit) != INT_MAX);
      lglpushstk (lgl, &lgl->saved, blit);
      cnt++;
      *p = -INT_MAX;
      offset = (1 << lglceilld (hts->count));
#ifndef NDEBUG
      assert (lglispow2 (offset));
      for (q = p + hts->count; q < p + offset; q++)
	assert (!*q);
#endif
      if (!p[offset]) p[offset] = INT_MAX;
    }
  LOG (3, "saved %d blits", cnt);
  move = 1;
  eow = lgl->wchs.top - 1;
  for (p = lgl->wchs.start + 1;  p < eow; p++) {
    blit = *p;
    if (blit == INT_MAX) {
      while (!p[1]) p++;
    } else {
      assert (blit == -INT_MAX);
      *p = move;
      LOG (3, "moving watch stack at %d to %d", p - lgl->wchs.start, move);
      while (abs (p[1]) != INT_MAX) p++, move++;
      move++;
    }
  }
  assert (p == eow);
  assert (*p == INT_MAX);
  recycled = lglcntstk (&lgl->wchs) - move - 1;
  LOG (2, "recycling %d watch stack words", recycled);
  cnt = 0;
  q = lgl->saved.start;
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = idx * sign;
      hts = lglhts (lgl, lit);
      if (!hts->offset) continue;
      p = lglhts2wchs (lgl, hts);
      hts->offset = *p;
      *p = *q++;
      cnt++;
    }
  assert (q == lgl->saved.top);
  assert (cnt == lglcntstk (&lgl->saved));
  LOG (3, "restored %d blits and moved all HTS offsets", cnt);
  lglclnstk (&lgl->saved);
  q = lgl->wchs.start + 1;
  for (p = q; p < eow; p++) {
    blit = *p;
    if (blit == INT_MAX) {
      while (!p[1]) p++;
    } else {
      while (*p != INT_MAX)
	*q++ = *p++;
      --p;
    }
  }
  assert (p == eow);
  assert (*p == INT_MAX);
  *q++ = INT_MAX;
  LOG (2, "shrinking global watcher stack by %d", lgl->wchs.top - q);
  lgl->wchs.top = q;
  lglredstk (lgl, &lgl->wchs, 0, 2);
  lgl->limits.dfg.pshwchs = lgl->stats.pshwchs + lgl->opts.defragint.val;
  lgl->limits.dfg.prgss = lgl->stats.prgss;
  lglrep (lgl, 2, 'f');
  lglstop (lgl);
}

static void lgldis (LGL * lgl) {
  int blit, nblit, tag, red, * p, * q, * eow, * w;
  int idx, sign, lit, other, other2;
  Stk bins, trns;
  Val val, val2;
  HTS * hts;
  assert (!lgl->level);
  CLR (bins); CLR (trns);
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = idx * sign;
      hts = lglhts (lgl, lit);
      if (!hts->offset) continue;
      val = lglval (lgl, lit);
      assert (hts->count > 0);
      if (val || lgliselim (lgl, lit))
	{ lglshrinkhts (lgl, hts, 0); continue; }
      assert (lglisfree (lgl, lit));
      assert (lglmtstk (&bins));
      assert (lglmtstk (&trns));
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	red = blit & REDCS;
	if (tag == IRRCS) continue;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (tag == LRGCS) continue;
	other = blit >> RMSHFT;
	val = lglval (lgl, other);
	if (val > 0) continue;
	if (lgliselim (lgl, other)) continue;
	if (tag == BINCS) {
	  assert (!val);
	  lglpushstk (lgl, &bins, blit);
	  continue;
	}
	assert (tag == TRNCS);
	other2 = *p;
	val2 = lglval (lgl, other2);
	if (val2 > 0) continue;
	if (lgliselim (lgl, other2)) continue;
	if (val < 0) {
	  assert (val < 0 && !val2);
	  nblit = red | (other2<<RMSHFT) | BINCS;
	  lglpushstk (lgl, &bins, nblit);
	  continue;
	}
	if (val2 < 0) {
	  assert (!val && val2 < 0);
	  nblit = red | (other<<RMSHFT) | BINCS;
	  lglpushstk (lgl, &bins, nblit);
	  continue;
	}
	assert (!val && !val2);
	lglpushstk (lgl, &trns, blit);
	lglpushstk (lgl, &trns, other2);
      }
      q = w;
      for (p = bins.start; p != bins.top; p++) *q++ = *p;
      for (p = trns.start; p != trns.top; p++) *q++ = *p;
      lglshrinkhts (lgl, hts, q - w);
      lglclnstk (&bins);
      lglclnstk (&trns);
    }
  lglrelstk (lgl, &bins);
  lglrelstk (lgl, &trns);
}

static void lglconnaux (LGL * lgl, int glue) {
  int lit, satisfied, lidx, size, red, act;
  const int * p, * c, * start, * top;
  int * q, * d;
  Stk * stk;
  Lir * lir;
  Val val;
  if (glue >= 0) {
    assert (glue < MAXGLUE);
    red = REDCS;
    lir = lgl->red + glue;
    stk = &lir->lits;
  } else red = 0, stk = &lgl->irr;
  c = start = q = stk->start;
  top = stk->top;
  while (c < top) {
    act = *c;
    if (act == REMOVED) {
      for (p = c + 1; p < top && *p == REMOVED; p++)
	;
      assert (p >= top || *p < NOTALIT || lglisact (*p));
      c = p;
      continue;
    }
    if (lglisact (act)) *q++ = *c++; else act = -1;
    p = c;
    d = q;
    satisfied = 0;
    while (assert (p < top), (lit = *p++)) {
      assert (lit < NOTALIT);
      if (satisfied) continue;
      val = lglval (lgl, lit);
      if (lgliselim (lgl, lit)) assert (lgl->eliminating), satisfied = 1;
      else if (val > 0) satisfied = 1;
      else if (!val) *q++ = lit;
    }
    if (satisfied || p == c + 1) {
      q = d - (act >= 0);
    } else if (!(size = q - d)) {
      q = d - (act >= 0);
      if (!lgl->mt) {
	LOG (1, "empty clause during connection garbage collection phase");
	lgl->mt = 1;
      }
    } else if (size == 1) {
      q = d - (act >= 0);
      LOG (1, "unit during garbage collection");
      lglunit (lgl, d[0]);
    } else if (size == 2) {
      q = d - (act >= 0);
      lglwchbin (lgl, d[0], d[1], red);
      lglwchbin (lgl, d[1], d[0], red);
    } else if (size == 3) {
      q = d - (act >= 0);
      lglwchtrn (lgl, d[0], d[1], d[2], red);
      lglwchtrn (lgl, d[1], d[0], d[2], red);
      lglwchtrn (lgl, d[2], d[0], d[1], red);
    } else {
      assert (size > 3);
      *q++ = 0;
      lidx = d  - start;
      if (red) {
	assert (lidx <= MAXREDLIDX);
	lidx <<= GLUESHFT;
	assert (0 <= lidx);
	lidx |= glue;
      }
      (void) lglwchlrg (lgl, d[0], d[1], red, lidx);
      (void) lglwchlrg (lgl, d[1], d[0], red, lidx);
    }
    c = p;
  }
  stk->top = q;
}

static void lglcon (LGL * lgl) {
  int glue;
  for (glue = -1; glue < MAXGLUE; glue++)
    lglconnaux (lgl, glue);
}

static void lglcount (LGL * lgl) {
  int idx, sign, lit, tag, blit, red, other, other2, glue, count;
  const int * p, * w, * c, * eow;
  HTS * hts;
  Lir * lir;
  lgl->stats.irr = 0;
  lgl->stats.red.bin = 0;
  lgl->stats.red.trn = 0;
  lgl->stats.red.lrg = 0;
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = lglhts (lgl, lit);
      if (!hts->offset) continue;
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	red = blit & REDCS;
	tag = blit & MASKCS;
	if (tag == LRGCS || tag == TRNCS) p++;
	if (tag == LRGCS) continue;
	assert (tag == BINCS || tag == TRNCS);
	other = blit >> RMSHFT;
	assert (abs (other) != abs (lit));
	if (abs (lit) >= abs (other)) continue;
	assert (2 == BINCS && 3 == TRNCS);
	if (tag == TRNCS) {
	  other2 = *p;
	  assert (abs (other2) != abs (lit));
	  assert (abs (other2) != abs (other));
	  if (abs (lit) >= abs (other2)) continue;
	}
	if (!red) lgl->stats.irr++;
	else if (tag == BINCS) lgl->stats.red.bin++;
	else assert (tag == TRNCS), lgl->stats.red.trn++;
      }
    }
  assert (lgl->stats.red.bin >= 0 && lgl->stats.red.trn >= 0);
  for (c = lgl->irr.start; c < lgl->irr.top; c++)
    if (!*c) lgl->stats.irr++;
  assert (lgl->stats.irr >= 0);
  if (lgl->stats.irr)
    LOG (1, "counted %d irredundant clauses", lgl->stats.irr);
  for (glue = 0; glue < MAXGLUE; glue++) {
    lir = lgl->red + glue;
    count = 0;
    for (c = lir->lits.start; c < lir->lits.top; c++)
      if (!*c) count++;
    if (count)
      LOG (1, "counted %d redundant clauses with glue %d", count, glue);
    lgl->stats.red.lrg += count;
    lgl->stats.lir[glue].clauses = count;
  }
  assert (lgl->stats.red.lrg >= 0);
  if (lgl->stats.red.bin)
    LOG (1, "counted %d binary redundant clauses altogether",
         lgl->stats.red.bin);
  if (lgl->stats.red.trn)
    LOG (1, "counted %d ternary redundant clauses altogether",
         lgl->stats.red.trn);
  if (lgl->stats.red.lrg)
    LOG (1, "counted %d large redundant clauses altogether",
         lgl->stats.red.lrg);
}

static int lglulit (int lit) { return 2*abs (lit) + (lit < 0); }

static int lglilit (int ulit) {
  int res = ulit/2;
  assert (res >= 1);
  if (ulit & 1) res = -res;
  return res;
}

static void lglincjwh (Flt * jwh, int lit, Flt inc) {
  int ulit = lglulit (lit);
  Flt old = jwh[ulit];
  Flt new = lgladdflt (old, inc);
  jwh[ulit] = new;
}

static void lglbias (LGL * lgl) {
  int idx, sign, lit, tag, blit, other, other2, glue;
  int red, npos, nneg, bias, size;
  const int *p, * w, * eow, * c;
  Flt * jwh, inc, pos, neg;
  HTS * hts;
  Stk * s;
  for (idx = 2; idx < lgl->nvars; idx++)
    lgl->avars[idx].phase = 0;
  if (lgl->opts.phase.val) return;
  NEW (jwh, 2*lgl->nvars);
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = lglhts (lgl, lit);
      if (!hts->offset) continue;
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (tag == LRGCS) continue;
	red = blit & REDCS;
	if (red) continue;
	other = blit >> RMSHFT;
	if (tag == BINCS) {
	  if (abs (other) < abs (lit)) continue;
	  inc = lglflt (-2, 1);
	  lglincjwh (jwh, lit, inc);
	  lglincjwh (jwh, other, inc);
	} else {
	  assert (tag == TRNCS);
	  other2 = *p;
	  if (abs (other) < abs (lit)) continue;
	  if (abs (other2) < abs (lit)) continue;
	  inc = lglflt (-3, 1);
	  lglincjwh (jwh, lit, inc);
	  lglincjwh (jwh, other, inc);
	  lglincjwh (jwh, other2, inc);
	}
      }
    }
  for (glue = -1; glue < MAXGLUE; glue++) {
    s = (glue < 0) ? &lgl->irr : &lgl->red[glue].lits;
    for (c = s->start; c < s->top; c = p + 1) {
      p = c;
      if (*p >= NOTALIT) continue;
      while (*p) p++;
      for (; *p; p++)
	;
      size = p - c;
      assert (size > 3);
      inc = lglflt (-size, 1);
      for (p = c; (other = *p); p++)
	lglincjwh (jwh, other, inc);
    }
  }
  nneg = npos = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    pos = jwh[lglulit (idx)];
    neg = jwh[lglulit (-idx)];
    if (pos > neg) { bias = 1; npos++; } else { bias = -1; nneg++; }
    if (lgl->opts.rebflip.val &&
        !(lglrand (lgl) % lgl->opts.rebflip.val)) bias *= -1;
    lgl->avars[idx].bias = bias;
  }
  DEL (jwh, 2*lgl->nvars);
  lglprt (lgl, 2, "%d (%.0f%%) positive phase bias, %d (%.0f%%) negative",
	     npos, lglpcnt (npos, lgl->nvars-2),
	     nneg, lglpcnt (nneg, lgl->nvars-2));
}

static void lglrebias (LGL * lgl) {
  int skip = lgl->limits.rebias.wasmaxdelta ? 0 : lglagile (lgl);
  if (skip) {
    lgl->stats.rebias.skipped++;
    LOG (1, "skipping rebias with agility %.0f%%", lglagile (lgl));
  } else {
    lglstart (lgl, &lgl->stats.tms.reb);
    lgl->stats.rebias.count++;
    LOG (1, "rebias %d", lgl->stats.rebias);
    lglbias (lgl);
    lglstop (lgl);
  }
  lglincrebiasl (lgl, skip);
}

static void lglrephrase (LGL * lgl) {
  AVar * av;
  int idx;
  lgl->stats.rephrased++;
  for (idx = 2; idx < lgl->nvars; idx++) {
    av = lgl->avars + idx;
    if (av->part != INT_MAX && av->part <= lgl->activepart) av->phase =0;
  }
  lgl->limits.rephrase += (lgl->limits.rephrase * lgl->opts.rphrfac.val)/100;
  lglrep (lgl, 1, 'P');
}

static void lglchkbcpclean (LGL * lgl) {
  assert (lgl->next == lglcntstk (&lgl->trail));
  assert (!lgl->conf.lit);
  assert (!lgl->mt);
}

static int lglcutwidth (LGL * lgl) {
  int lidx, res, l4, r4, b4, l10, r10, b10, m, oldbias;
  int idx, sign, lit, blit, tag, red, other, other2;
  const int * p, * w, * eow, * c, * q;
  int * widths, max, cut, min4, min10;
  int64_t sum, avg;
  HTS * hts;
  if (lgl->nvars <= 2) return 0;
  oldbias = lgl->bias;
  assert (abs (oldbias) <= 1);
  if (abs (lgl->opts.bias.val) <= 1) {
    lgl->bias = lgl->opts.bias.val;
    goto DONE;
  }
  min4 = min10 = INT_MAX;
  sum = max = cut = 0;
  NEW (widths, lgl->nvars);
  l4 = 2 + (lgl->nvars - 2 + 3)/4;
  r4 = 2 + (3*(lgl->nvars - 2)+3)/4;
  assert (2 <= l4 && l4 <= r4 && r4 <= lgl->nvars);
  l10 = 2 + (lgl->nvars - 2 + 9)/10;
  r10 = 2 + (9*(lgl->nvars - 2)+9)/10;
  assert (2 <= l10 && l10 <= r10 && r10 <= lgl->nvars);
  b4 = b10 = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    for (sign = -1; sign <= 1; sign += 2) {
      lit = idx * sign;
      hts = lglhts (lgl, lit);
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	red = blit & REDCS;
	tag = blit & MASKCS;
	other = abs (blit >> RMSHFT);
	if (tag == BINCS) {
	  if (red) continue;
	  if (other > idx) widths[other]++, cut++;
	} else if (tag == TRNCS) {
	  other2 = abs (*++p);
	  if (red) continue;
	  if (other > idx) widths[other]++, cut++;
	  if (other2 > idx) widths[other2]++, cut++;
	} else {
	  assert (tag == LRGCS);
	  lidx = *++p;
	  if (red) continue;
	  c = lglidx2lits (lgl, red, lidx);
	  for (q = c; (other = abs (*q)); q++) {
	    if (other == idx) continue;
	    if (other > idx) widths[other]++, cut++;
	  }
	}
      }
    }
    assert (0 <= cut && 0 <= widths[idx]);
    cut -= widths[idx];
    assert (cut >= 0);
    if (cut > max) max = cut;
    if (l4 <= idx && idx <= r4 && cut < min4) b4 = idx, min4 = cut;
    if (l10 <= idx && idx <= r10 && cut < min10) b10 = idx, min10 = cut;
    sum += cut;
    assert (sum >= 0);
  }
  DEL (widths, lgl->nvars);
  assert (lgl->nvars > 0);
  avg = sum / (long long) lgl->nvars;
  assert (avg <= INT_MAX);
  res = (int) avg;
  lglprt (lgl, 2,
    "cut width %d, max %d, min4 %d at %.0f%%, min10 %d at %.0f%%",
    res, max,
    min4, lglpcnt ((b4 - 2), lgl->nvars - 2),
    min10, lglpcnt ((b10 - 2), lgl->nvars - 2));
  m = (lgl->nvars + 2)/2;
  if (b4 < m && b10 < m) lgl->bias = -1;
  if (b4 > m && b10 > m) lgl->bias = 1;
DONE:
  assert (abs (lgl->bias <= 1));
  if (oldbias != lgl->bias) lgldreschedule (lgl);
  lglprt (lgl, 2, "decision bias %d", lgl->bias);
  return res;
}

static int lglmaplit (int * map, int lit) {
  return map [ abs (lit) ] * lglsgn (lit);
}

static void lglmapstk (LGL * lgl, int * map, Stk * lits) {
  int * p, * eol;
  eol = lits->top;
  for (p = lits->start; p < eol; p++)
    *p = lglmaplit (map, *p);
}

static void lglmapglue (LGL * lgl, int * map, Stk * lits) {
  int * p, * eol;
  eol = lits->top;
  for (p = lits->start; p < eol; p++)
    if (!lglisact (*p)) *p = lglmaplit (map, *p);
}

static void lglmaplits (LGL * lgl, int * map) {
  int glue;
  lglmapstk (lgl, map, &lgl->irr);
  for (glue = 0; glue < MAXGLUE; glue++)
    lglmapglue (lgl, map, &lgl->red[glue].lits);
}

static void lglmapvars (LGL * lgl, int * map, int nvars) {
  int i, oldnvars = lgl->nvars;
  DVar * dvars;
  AVar * avars;
  Val * vals;
  int * i2e;

  if (nvars > 2) assert (nvars <= oldnvars);
  else nvars = 0;

  NEW (vals, nvars);
  for (i = 2; i < oldnvars; i++)
    if (lglisfree (lgl, i))
      vals[map[i]] = lgl->vals[i];
  DEL (lgl->vals, lgl->szvars);
  lgl->vals = vals;

  NEW (i2e, nvars);
  for (i = 2; i < oldnvars; i++)
    if (lglisfree (lgl, i))
      i2e[map[i]] = lgl->i2e[i];
  DEL (lgl->i2e, lgl->szvars);
  lgl->i2e = i2e;

  NEW (dvars, nvars);
  for (i = 2; i < oldnvars; i++)
    if (lglisfree (lgl, i))
      dvars[map[i]] = lgl->dvars[i];
  DEL (lgl->dvars, lgl->szvars);
  lgl->dvars = dvars;

  NEW (avars, nvars);
  for (i = 2; i < oldnvars; i++)
    if (lglisfree (lgl, i))
      avars[map[i]] = lgl->avars[i];
  DEL (lgl->avars, lgl->szvars);
  lgl->avars = avars;

  lgl->nvars = lgl->szvars = nvars;
  lgl->stats.fixed.current = 0;
}

static void lglmaphts (LGL * lgl, int * map) {
  int idx, sign, lit, * w, *eow, * p, other, other2, blit, tag, red;
  int newblit, newother, newother2;
  HTS * hts;
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = lglhts (lgl, lit);
      if (!hts->count) continue;
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	assert (tag == BINCS || tag == TRNCS || tag == LRGCS);
	red = blit & REDCS;
	other = blit >> RMSHFT;
	newother = lglmaplit (map, other);
	newblit = (newother << RMSHFT) | tag | red;
	*p = newblit;
	if (tag == BINCS) continue;
	other2 = *++p;
	if (tag == LRGCS) continue;
	assert (tag == TRNCS);
	newother2 = lglmaplit (map, other2);
	*p = newother2;
      }
    }
}

static void lglmaptrail (LGL * lgl, int * map) {
  int * p, * q, src, dst;
  for (p = lgl->trail.start; p < lgl->trail.top; p++)
    if (lglevel (lgl, *p) > 0) break;
  for (q = lgl->trail.start; p < lgl->trail.top; p++) {
    src = *p;
    assert (lglevel (lgl, src) > 0);
    dst = lglmaplit (map, src);
    *q++ = dst;
  }
  lgl->trail.top = q;
  lgl->flushed = lgl->next = lglcntstk (&lgl->trail);
}

static int lglptrjmp (int * repr, int max, int start) {
#ifndef NDEBUG
  int prev = 0, count = 0;
#endif
  int next, idx, res, sgn, tmp;
  assert (repr);
  next = start;
  do {
    res = next;
    idx = abs (res);
    assert (idx <= max);
    sgn = lglsgn (res);
    next = repr[idx];
    next *= sgn;
#ifndef NDEBUG
    if (prev || next) assert (prev != next);
    prev = res;
    assert (count <= max);
#endif
  } while (next);
  tmp = start;
  while (tmp != res) {
    idx = abs (tmp), sgn = lglsgn (tmp);
    next = repr[idx] * sgn;
    repr[idx] = sgn * res;
    tmp = next;
  }
  return res;
}

static int lglirepr (LGL * lgl, int lit) {
  assert (lgl->repr);
  return lglptrjmp (lgl->repr, lgl->nvars - 1, lit);
}

static void lglmapext (LGL * lgl, int * map) {
  int eidx, ilit, mlit;
  Ext * ext;
  for (eidx = 1; eidx <= lgl->maxext; eidx++) {
    ext = lgl->ext + eidx;
    if (ext->equiv) continue;
    ilit = ext->repr;
    mlit = lglmaplit (map, ilit);
    LOG (3, "mapping external %d to internal %d", eidx, mlit);
    ext->repr = mlit;
  }
}

static void lglmapass (LGL * lgl, int * map) {
  int iass = lgl->assume, mass;
  if (!iass) return;
  mass = lglmaplit (map, iass);
  LOG (2, "mapping previous internal assumption %d to %d", iass, mass);
  lgl->assume = mass;
}

#if !defined(NDEBUG) && !defined(NLGLPICOSAT)
static void lglpicosataddstk (const Stk * stk) {
  const int * p;
  int lit;
  for (p = stk->start; p < stk->top; p++) {
    lit = *p;
    if (lit >= NOTALIT) continue;
    picosat_add (lit);
  }
}

static void lglpicosataddunits (LGL * lgl) {
  int idx, val;
  assert (!lgl->level);
  assert (lgl->picosat.init);
  for (idx = 2; idx < lgl->nvars; idx++) {
    val = lglval (lgl, idx);
    assert (!val);
  }
}

static void lglpicosataddhts (LGL * lgl) {
  int idx, sign, lit, tag, blit, other, other2;
  const int * w, * p, * eow;
  HTS * hts;
  assert (lgl->picosat.init);
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = lglhts (lgl, lit);
      if (!hts->count) continue;
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == BINCS) {
	  other = blit >> RMSHFT;
	  if (abs (other) < idx) continue;
	  picosat_add (lit);
	  picosat_add (other);
	  picosat_add (0);
	} else if (tag == TRNCS) {
	  other = blit >> RMSHFT;
	  other2 = *++p;
	  if (abs (other) < idx) continue;
	  if (abs (other2) < idx) continue;
	  picosat_add (lit);
	  picosat_add (other);
	  picosat_add (other2);
	  picosat_add (0);
	} else if (tag == LRGCS) p++;
	else assert (lgl->dense && tag == IRRCS);
      }
    }
}
#endif

static void lglpicosatchkall (LGL * lgl) {
#if !defined(NDEBUG) && !defined(NLGLPICOSAT)
  int res;
  if (lgl->tid >= 0 || !lgl->opts.check.val) return;
  lglpicosatinit (lgl);
  if (lgl->opts.check.val >= 2) {
    if (lgl->assume) picosat_assume (lgl->assume);
    res = picosat_sat (-1);
    LOG (1, "PicoSAT returns %d", res);
    if (lgl->picosat.res) assert (res == lgl->picosat.res);
    lgl->picosat.res = res;
  }
  if (picosat_inconsistent ()) {
    assert (!lgl->picosat.res || lgl->picosat.res == 20);
    lgl->picosat.res = 20;
  }
#endif
}

static void lglpicosatrestart (LGL * lgl) {
#if !defined(NDEBUG) && !defined(NLGLPICOSAT)
  if (lgl->tid >= 0 || !lgl->opts.check.val) return;
  if (lgl->picosat.init) {
    picosat_reset ();
    LOG (1, "PicoSAT reset");
    lgl->picosat.init = 0;
  }
  lglpicosatinit (lgl);
  lglpicosataddunits (lgl);
  if (lgl->mt) picosat_add (0);
  lglpicosataddhts (lgl);
  lglpicosataddstk (&lgl->irr);
#endif
}

static void lglmap (LGL * lgl) {
  int idx, ridx, size, dst, count, * map, oldnvars, repr;
  AVar * av, * rv;;
  Val val;
#ifndef NLGLPICOSAT
  lglpicosatchkall (lgl);
#endif
  assert (!lgl->level);
  size = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    av = lglavar (lgl, idx);
    if (av->type == ELIMVAR) continue;
    if (av->type != FREEVAR) continue;
    assert (!lglval (lgl, idx));
    size++;
  }
  LOG (1, "mapping %d remaining variables", size);
  oldnvars = lgl->nvars;
  NEW (map, lglmax (oldnvars, 2));
  map[0] = 0, map[1] = 1;
  count = 0;
  dst = 2;
  for (idx = 2; idx < lgl->nvars; idx++) {
    if (map[idx]) continue;
    av = lglavar (lgl, idx);
    if (av->type == FREEVAR) {
      assert (idx > 0);
      if (map[idx]) { assert (map[idx] < idx); continue; }
      LOG (3, "mapping free %d to %d", idx, count + 2);
      map[idx] = count + 2;
      count++;
    } else if (av->type == EQUIVAR) {
      assert (lgl->repr);
      assert (!map[idx]);
      repr = lglirepr (lgl, idx);
      assert (repr != idx);
      ridx = abs (repr);
      if (ridx < idx) {
	assert (map[ridx]);
      } else if (!map[ridx]) {
	rv = lglavar (lgl, repr);
	if (rv->type == FREEVAR) {
	  map[ridx] = count + 2;
	  count++;
	} else {
	  assert (lglavar (lgl, repr)->type == FIXEDVAR);
	  val = lgl->vals[ridx];
	  LOG (3, "mapping assigned representative %d to %d", ridx, val);
	}
      }
      dst = lglmaplit (map, repr);
      LOG (3, "mapping equivalent %d to %d", idx, dst);
      map[idx] = dst;
    } else if (av->type == FIXEDVAR) {
      val = lgl->vals[idx];
      assert (val);
      LOG (3, "mapping assigned %d to %d", idx, (int) val);
      map[idx] = val;
    } else {
      assert (av->type == ELIMVAR);
      assert (!lglifrozen (lgl, idx));
      map[idx] = 0;
    }
  }
  assert (count == size);
  lglmaptrail (lgl, map);
  lglmapvars (lgl, map, size + 2);
  lglmaplits (lgl, map);
  lglmapstk (lgl, map, &lgl->dsched);
  lglmapext (lgl, map);
  lglmapass (lgl, map);
  assert (lglmtstk (&lgl->clause));
  lglmaphts (lgl, map);
  DEL (map, lglmax (oldnvars, 2));
  if (lgl->repr) DEL (lgl->repr, oldnvars);
  lgldreschedule (lgl);
  lglpicosatrestart (lgl);
  lgl->unassigned = size;
}

static int lglfixedoreq (LGL * lgl) {
  return lgl->stats.fixed.sum + lgl->stats.equiv.sum;
}

static void lglfitlirs (LGL * lgl) {
  int glue;
  for (glue = 0; glue < MAXGLUE; glue++)
    lglfitlir (lgl, lgl->red + glue);
}

static void lglgc (LGL * lgl) {
  lglchkred (lgl);
  if (!lgl->eliminating && !lgl->blocking &&
      lglfixedoreq (lgl) == lgl->limits.gc.fixedoreq) return;
  if (lgl->decomposing) lglstart (lgl, &lgl->stats.tms.gcd);
  else if (lgl->lifting) lglstart (lgl, &lgl->stats.tms.gcl);
  else if (lgl->eliminating) lglstart (lgl, &lgl->stats.tms.gce);
  else if (lgl->blocking) lglstart (lgl, &lgl->stats.tms.gcb);
  else if (lgl->unhiding) lglstart (lgl, &lgl->stats.tms.gcu);
  else lglstart (lgl, &lgl->stats.tms.gc);
  lglchkbcpclean (lgl);
  lglrep (lgl, 2, 'g');
  lgl->stats.gcs++;
  if (lgl->level > 0) lglbacktrack (lgl, 0);
  for (;;) {
    lgldis (lgl);
    lglcon (lgl);
    if (!lgl->mt && lgl->next == lglcntstk (&lgl->trail)) break;
    if (!lglbcp (lgl)) {
      assert (!lgl->mt);
      LOG (1, "empty clause after propagating garbage collection unit");
      lgl->mt = 1;
      break;
    }
  }
  lglcount (lgl);
  lgldreschedule (lgl);
  lglmap (lgl);
  if (!lgl->simp) {
    lgl->limits.gc.vinc += lgl->opts.gcvintinc.val;
    lgl->limits.gc.cinc += lgl->opts.gccintinc.val;
  }
  lglfitlirs (lgl);
  lgl->limits.gc.visits = lgl->stats.visits.search + lgl->limits.gc.vinc;
  lgl->limits.gc.confs = lgl->stats.confs + lgl->limits.gc.cinc;
  lgl->limits.gc.irr = lgl->stats.irr + lgl->opts.gcirrintinc.val;
  lgl->limits.gc.fixedoreq = lglfixedoreq (lgl);
  lglrep (lgl, 2, 'c');
  lglstop (lgl);
  lglchkred (lgl);
}

static void lgliassume (LGL * lgl, int lit) {
  if (!lgl->level++) lgl->decision = lit;
  lglpushcontrol (lgl, lit);
  assert (lglcntctk (&lgl->control) == lgl->level + 1);
  LOG (2, "assuming %d", lit);
  lglassign (lgl, lit, DECISION, 0);
}

static void lgldeactivate (LGL * lgl, int part) {
  AVar *av;
  int idx;
  assert (part < INT_MAX);
  for (idx = 2; idx < lgl->nvars; idx++) {
    av = lglavar (lgl, idx);
    if (av->part > part) continue;
    LOG (3, "deactivating variable %d", idx);
    av->part = INT_MAX;
  }
  lgldreschedule (lgl);
  lglprt (lgl, 2, "deactivated components up to %d", part);
}

static int lglrandec (LGL * lgl) {
  unsigned size, pos, start, delta;
  int lit;
  lgl->limits.randec = lgl->stats.decisions;
  lgl->limits.randec += lgl->opts.randecint.val/2;
  lgl->limits.randec += lglrand (lgl) % lgl->opts.randecint.val;
  size = lglcntstk (&lgl->dsched);
  if (!size) return 0;
  pos = start = lglrand (lgl) % size;
  lit = lglpeek (&lgl->dsched, pos);
  assert (abs (lit) > 1);
  if (lglval (lgl, lit)) {
    delta = lglrand (lgl) % size;
    if (size == 1) return 0;
    if (!delta) delta++;
    while (lglgcd (delta, size) != 1)
      if (++delta == size) delta = 1;
    do {
      pos += delta;
      if (pos >= size) pos -= size;
      if (pos == start) return 0;
      lit = lglpeek (&lgl->dsched, pos);
      assert (abs (lit) > 1);
    } while (lglval (lgl, lit));
  }
  lgl->stats.randecs++;
  return lit;
}

static int lgldecide (LGL * lgl) {
  int lit, bias;
  AVar * av;
  lglchkbcpclean (lgl);
  if (!lgl->unassigned) return 0;
  if (!lgl->level && lgl->assume && !lglcval (lgl, lgl->assume)) {
    lit = lgl->assume;
    LOG (2, "using assumption %d", lit);
  } else {
    assert (lgl->level || !lgl->assume || lglcval (lgl, lgl->assume) > 0);
    if (lgl->opts.randec.val &&
	lgl->limits.randec <= lgl->stats.decisions) {
      lit = lglrandec (lgl);
      LOG (2, "random decision %d", lit);
    } else {
      for (;;) {
	if (lglmtstk (&lgl->dsched)) return 0;
	lit = lglpopdsched (lgl);
	if (!lglval (lgl, lit)) {
	  LOG (2, "best decision %d", lit);
	  av = lglavar (lgl, lit);
	  if (lgl->opts.deactivate.val && av->part > lgl->activepart) {
	    assert (lgl->partitioned);
	    if (av->part < INT_MAX) lgldeactivate (lgl, av->part - 1);
	    lgl->activepart = av->part;
	    lglprt (lgl, 2, "activated component %d", lgl->activepart);
	  }
	  break;
	}
      }
    }
    av = lglavar (lgl, lit);
    if (!av->phase) {
      bias = lgl->opts.phase.val;
      if (!bias) bias = av->bias;
      av->phase = bias;
    }
    if (av->phase < 0) lit = -lit;
  }
  LOG (2, "next decision %d", lit);
  lgl->stats.decisions++;
  lgl->stats.height += lgl->level;
  lgliassume (lgl, lit);
  assert (lgldecision (lgl, lit));
  return 1;
}

static void lgldcpdis (LGL * lgl) {
  int idx, sign, lit, tag, blit, red, other, other2, i;
  const int * w, * p, * eow;
  Val val;
  HTS * hts;
  Stk * s;
  assert (lglmtstk (&lgl->dis.irr.bin));
  assert (lglmtstk (&lgl->dis.irr.trn));
  assert (lglmtstk (&lgl->dis.red.bin));
  assert (lglmtstk (&lgl->dis.red.trn));
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = lglhts (lgl, lit);
      if (!hts->offset) continue;
      assert (hts->count > 0);
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      hts->count = hts->offset = 0;
      val = lglval (lgl, lit);
      if (val > 0) continue;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (tag == LRGCS) continue;
	other = blit >> RMSHFT;
	if (abs (other) < idx) continue;
	val = lglval (lgl, other);
	if (val > 0) continue;
	red = blit & REDCS;
	if (red && !lglisfree (lgl, other)) continue;
	if (tag == BINCS) {
	  s = red ? &lgl->dis.red.bin : &lgl->dis.irr.bin;
	} else {
	  assert (tag == TRNCS);
	  other2 = *p;
	  if (abs (other2) < idx) continue;
	  val = lglval (lgl, other2);
	  if (val > 0) continue;
	  if (red && !lglisfree (lgl, other2)) continue;
	  s = red ? &lgl->dis.red.trn : &lgl->dis.irr.trn;
	  lglpushstk (lgl, s, other2);
	}
	lglpushstk (lgl, s, other);
	lglpushstk (lgl, s, lit);
	lglpushstk (lgl, s, 0);
      }
    }
  lglrststk (&lgl->wchs, 2);
  lgl->wchs.top[-1] = INT_MAX;
  for (i = 0; i < MAXLDFW; i++) lgl->freewchs[i] = INT_MAX;
  lgl->nfreewchs = 0;
}

static void lgldcpclnstk (LGL * lgl, int red, Stk * s) {
  int oldsz, newsz, lit, mark, satisfied, repr, act;
  const int * p, * c, * eos = s->top;
  int * start, * q, * r, * d;
  Stk * t;
  Val val;
  q = start = s->start;
  for (c = q; c < eos; c = p + 1) {
    act = *c;
    if (act == REMOVED) {
      for (p = c + 1; p < eos && *p == REMOVED; p++)
	;
      assert (p >= eos || *p < NOTALIT || lglisact (*p));
      p--;
      continue;
    }
    if (lglisact (act)) *q++ = *c++; else act = -1;
    d = q;
    satisfied = 0;
    for (p = c; assert (p < eos), (lit = *p); p++) {
      assert (lit < NOTALIT);
      if (satisfied) continue;
      repr = lglirepr (lgl, lit);
      val = lglval (lgl, repr);
      if (val > 0) { satisfied = 1; continue; }
      if (val < 0) continue;
      mark = lglmarked (lgl, repr);
      if (mark < 0) { satisfied = 1; continue; }
      if (mark > 0) continue;
      lglmark (lgl, repr);
      *q++ = repr;
    }
    oldsz = p - c;
    for (r = d; r < q; r++) lglunmark (lgl, *r);
    if (satisfied || !oldsz) { q = d - (act >= 0); continue; }
    newsz = q - d;
    if (newsz >= 4) {
      assert (act < 0 || d[-1] == act);
      *q++ = 0;
      assert (d <= c);
    } else if (!newsz) {
      LOG (1, "found empty clause while cleaning decompostion");
      lgl->mt = 1;
      q = d - (act >= 0);
    } else if (newsz == 1) {
      LOG (1, "new unit %d while cleaning decomposition", d[0]);
      lglunit (lgl, d[0]);
      q = d - (act >= 0);
    } else if (newsz == 2) {
      t = red ? &lgl->dis.red.bin : &lgl->dis.irr.bin;
      if (s != t) {
	lglpushstk (lgl, t, d[0]);
	lglpushstk (lgl, t, d[1]);
	lglpushstk (lgl, t, 0);
	q = d - (act >= 0);
      } else *q++ = 0;
    } else {
      assert (newsz == 3);
      t = red ? &lgl->dis.red.trn : &lgl->dis.irr.trn;
      if (s != t) {
	lglpushstk (lgl, t, d[0]);
	lglpushstk (lgl, t, d[1]);
	lglpushstk (lgl, t, d[2]);
	lglpushstk (lgl, t, 0);
	q = d - (act >= 0);
      } else *q++ = 0;
    }
  }
  s->top = q;
}

static void lgldcpconnaux (LGL * lgl, int red, int glue, Stk * s) {
  int * start = s->start, * q, * d, lit, size, lidx, act;
  const int * p, * c, * eos = s->top;
  assert (red == 0 || red == REDCS);
  assert (!glue || red);
  q = start;
  for (c = q; c < eos; c = p + 1) {
    if (lglisact (act = *c)) *q++ = *c++; else act = -1;
    d = q;
    for (p = c; (lit = *p); p++) {
      assert (!lgl->repr[abs (lit)]);
      assert (!lgl->vals[abs (lit)]);
      *q++ = lit;
    }
    size = q - d;
    if (size == 2) {
      q = d - (act >= 0);
      lglwchbin (lgl, d[0], d[1], red);
      lglwchbin (lgl, d[1], d[0], red);
    } else if (size == 3) {
      q = d - (act >= 0);
      lglwchtrn (lgl, d[0], d[1], d[2], red);
      lglwchtrn (lgl, d[1], d[0], d[2], red);
      lglwchtrn (lgl, d[2], d[0], d[1], red);
    } else {
      assert (size > 3);
      *q++ = 0;
      lidx = d - start;
      if (red) {
	assert (lidx <= MAXREDLIDX);
	lidx <<= GLUESHFT;
	assert (0 <= lidx);
	lidx |= glue;
      }
      (void) lglwchlrg (lgl, d[0], d[1], red, lidx);
      (void) lglwchlrg (lgl, d[1], d[0], red, lidx);
    }
  }
  s->top = q;
}

static void lgldcpcon (LGL * lgl) {
  Lir * lir;
  int glue;
  lgldcpconnaux (lgl, 0, 0, &lgl->dis.irr.bin);
  lgldcpconnaux (lgl, REDCS, 0, &lgl->dis.red.bin);
  lgldcpconnaux (lgl, 0, 0, &lgl->dis.irr.trn);
  lgldcpconnaux (lgl, REDCS, 0, &lgl->dis.red.trn);
  lglrelstk (lgl, &lgl->dis.irr.bin);
  lglrelstk (lgl, &lgl->dis.irr.trn);
  lglrelstk (lgl, &lgl->dis.red.bin);
  lglrelstk (lgl, &lgl->dis.red.trn);
  lgldcpconnaux (lgl, 0, 0, &lgl->irr);
  for (glue = 0; glue < MAXGLUE; glue++) {
    lir = lgl->red + glue;
    lgldcpconnaux (lgl, REDCS, glue, &lir->lits);
  }
}

static void lgldcpcln (LGL * lgl) {
  int glue, old, rounds = 0;
  Lir * lir;
  do {
    rounds++;
    old = lgl->stats.fixed.current;
    lgldcpclnstk (lgl, 0, &lgl->irr);
    lgldcpclnstk (lgl, 0, &lgl->dis.irr.bin);
    lgldcpclnstk (lgl, 0, &lgl->dis.irr.trn);
    lgldcpclnstk (lgl, REDCS, &lgl->dis.red.bin);
    lgldcpclnstk (lgl, REDCS, &lgl->dis.red.trn);
    for (glue = 0; glue < MAXGLUE; glue++) {
      lir = lgl->red + glue;
      lgldcpclnstk (lgl, REDCS, &lir->lits);
    }
  } while (old < lgl->stats.fixed.current);
  LOG (1, "iterated %d decomposition cleaning rounds", rounds);
}

static void lglemerge (LGL * lgl, int ilit0, int ilit1) {
  int elit0 = lgl->i2e[abs (ilit0)] * lglsgn (ilit0);
  int elit1 = lgl->i2e[abs (ilit1)] * lglsgn (ilit1);
  int repr0 = lglerepr (lgl, elit0);
  int repr1 = lglerepr (lgl, elit1);
  Ext * ext0 = lglelit2ext (lgl, repr0);
#ifndef NDEBUG
  Ext * ext1 = lglelit2ext (lgl, repr1);
  int repr = repr1;
#endif
  assert (abs (repr0) != abs (repr1));
  if (repr0 < 0) repr0 *= -1, repr1 *= -1;
  ext0->equiv = 1;
  ext0->repr = repr1;
  LOG (2, "merging external literals %d and %d", repr0, repr1);
  assert (lglerepr (lgl, elit0) == repr);
  assert (lglerepr (lgl, elit1) == repr);
  assert (!(ext0->frozen || ext0->tmpfrozen) ||
            ext1->frozen || ext1->tmpfrozen);
}

static void lglimerge (LGL * lgl, int lit, int repr) {
  int idx = abs (lit);
  AVar * av = lglavar (lgl, idx);
  assert (!lglifrozen (lgl, lit) || lglifrozen (lgl, repr));
  if (lit < 0) repr = -repr;
  assert (av->type == FREEVAR);
  assert (lgl->repr);
  av->type = EQUIVAR;
  lgl->repr[idx] = repr;
  lgl->stats.prgss++;
  lgl->stats.equiv.sum++;
  lgl->stats.equiv.current++;
  assert (lgl->stats.equiv.sum > 0);
  assert (lgl->stats.equiv.current > 0);
#ifndef NLGLPICOSAT
  lglpicosatchkclsarg (lgl, idx, -repr, 0);
  lglpicosatchkclsarg (lgl, -idx, repr, 0);
#endif
  lglemerge (lgl, idx, repr);
}

static void lglfreezer (LGL * lgl) {
  int frozen, melted, tmpfrozen, elit, erepr;
  Ext * ext, * rext;
  if (lgl->frozen) return;
  for (elit = 1; elit <= lgl->maxext; elit++) lgl->ext[elit].tmpfrozen =0;
  tmpfrozen = frozen = 0;
  if (lgl->eassume) {
    assert (lgl->assume);
    ext = lglelit2ext (lgl, lgl->eassume);
    assert (!ext->melted);
    assert (!ext->eliminated);
    assert (!ext->blocking);
    if (!ext->frozen) {
      assert (!ext->tmpfrozen);
      ext->tmpfrozen = 1;
      tmpfrozen++;
      LOG (2, "temporarily freezing external assumption %d", lgl->eassume);
      erepr = lglerepr (lgl, lgl->eassume);
      rext = lglelit2ext (lgl, erepr);
      if (ext != rext && !rext->frozen) {
	assert (!rext->tmpfrozen);
	assert (!rext->melted);
	assert (!rext->equiv);
	assert (!rext->eliminated);
	assert (!rext->blocking);
	LOG (2, "temporarily freezing external assumption literal %d", erepr);
	rext->tmpfrozen = 1;
	tmpfrozen++;
      }
    }
  } else assert (!lgl->assume);
  for (elit = 1; elit <= lgl->maxext; elit++) {
    ext = lglelit2ext (lgl, elit);
    if (!ext->frozen) continue;
    frozen++;
    assert (!ext->melted);
    assert (!ext->eliminated);
    assert (!ext->blocking);
    erepr = lglerepr (lgl, elit);
    rext = lglelit2ext (lgl, erepr);
    if (ext == rext) continue;
    if (rext->frozen) continue;
    if (rext->tmpfrozen) continue;
    assert (!rext->melted);
    assert (!rext->equiv);
    assert (!rext->eliminated);
    assert (!rext->blocking);
    LOG (2, "temporarily freezing external literal %d", erepr);
    rext->tmpfrozen = 1;
    tmpfrozen++;
  }
  melted = 0;
  for (elit = 1; elit <= lgl->maxext; elit++) {
    ext = lglelit2ext (lgl, elit);
    if (ext->frozen) continue;
    if (ext->melted) continue;
    if (ext->tmpfrozen) continue;
    LOG (2, "permanently melted external %d", elit);
    ext->melted = 1;
    melted++;
  }
  LOG (2, "found %d frozen external variables", frozen);
  LOG (2, "temporarily frozen %d external variables", tmpfrozen);
  LOG (2, "permanently melted %d external variables", melted);
  lgl->frozen = 1;
  LOG (2, "frozen solver");
}

static int lglcmprepr (LGL * lgl, int a, int b) {
  int f = lglifrozen (lgl, a), g = lglifrozen (lgl, b), res;
  if ((res = g - f)) return res;
  if ((res = (abs (a) - abs (b)))) return res;
  return a - b;
}

static int lgltarjan (LGL * lgl) {
  int * dfsimap, * mindfsimap, idx, oidx, sign, lit, blit, tag, other;
  int dfsi, mindfsi, ulit, uother, tmp, repr, res, sgn, frozen;
  const int * p, * w, * eow;
  Stk stk, component;
  AVar * av;
  HTS * hts;
  if (!lgl->nvars) return 1;
  lglstart (lgl, &lgl->stats.tms.trj);
  lglfreezer (lgl);
  dfsi = 0;
  NEW (dfsimap, 2*lgl->nvars);
  NEW (mindfsimap, 2*lgl->nvars);
  NEW (lgl->repr, lgl->nvars);
  CLR (stk); CLR (component);
  res = 1;
  for (idx = 2; idx < lgl->nvars; idx++) {
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      ulit = lglulit (lit);
      tmp = dfsimap[ulit];
      if (tmp) continue;
      lglpushstk (lgl, &stk, lit);
      while (!lglmtstk (&stk)) {
	lit = lglpopstk (&stk);
	if (lit) {
	  ulit = lglulit (lit);
	  if (dfsimap[ulit]) continue;
	  dfsimap[ulit] = mindfsimap[ulit] = ++dfsi;
	  lglpushstk (lgl, &component, lit);
	  assert (dfsi > 0);
	  lglpushstk (lgl, &stk, lit);
	  lglpushstk (lgl, &stk, 0);
	  hts = lglhts (lgl, -lit);
	  if (!hts->offset) continue;
	  assert (hts->count > 0);
	  w = lglhts2wchs (lgl, hts);
	  eow = w + hts->count;
	  for (p = w; p < eow; p++) {
	    blit = *p;
	    tag = blit & MASKCS;
	    if (tag != BINCS) { p++; continue; }
	    other = blit >> RMSHFT;
	    uother = lglulit (other);
	    tmp = dfsimap[uother];
	    if (tmp) continue;
	    lglpushstk (lgl, &stk, other);
	  }
	} else {
	  assert (!lglmtstk (&stk));
	  lit = lglpopstk (&stk);
	  ulit = lglulit (lit);
	  mindfsi = dfsimap[ulit];
	  assert (mindfsi);
	  hts = lglhts (lgl, -lit);
	  w = lglhts2wchs (lgl, hts);
	  eow = w + hts->count;
	  for (p = w; p < eow; p++) {
	    blit = *p;
	    tag = blit & MASKCS;
	    if (tag != BINCS) { p++; continue; }
	    other = blit >> RMSHFT;
	    uother = lglulit (other);
	    tmp = mindfsimap[uother];
	    if (tmp >= mindfsi) continue;
	    mindfsi = tmp;
	  }
	  if (mindfsi == dfsimap[ulit]) {
	    repr = lit;
	    frozen = lglifrozen (lgl, repr);
	    for (p = component.top - 1; (other = *p) != lit; p--) {
	      if (lglcmprepr (lgl, other, repr) < 0) repr = other;
	      if (!frozen && lglifrozen (lgl, other)) frozen = 1;
	    }
	    while ((other = lglpopstk (&component)) != lit) {
	      mindfsimap[lglulit (other)] = INT_MAX;
	      if (other == repr) continue;
	      if (other == -repr) {
		LOG (1, "empty clause since repr[%d] = %d", repr, other);
		lgl->mt = 1; res = 0; goto DONE;
	      }
	      sgn = lglsgn (other);
	      oidx = abs (other);
	      tmp = lgl->repr[oidx];
	      if (tmp == sgn * repr) continue;
	      LOG (2, "repr[%d] = %d", oidx, sgn * repr);
	      if (tmp) {
		LOG (1, "empty clause since repr[%d] = %d and repr[%d] = %d",
		     oidx, tmp, oidx, sgn * repr);
		lgl->mt = 1; res = 0; goto DONE;
	      } else {
		av = lglavar (lgl, oidx);
		assert (sgn*oidx == other);
		if (av->type == FREEVAR) lglimerge (lgl, other, repr);
		else assert (av->type == FIXEDVAR);
	      }
	    }
	    mindfsimap[lglulit (lit)] = INT_MAX;
	    if (frozen) {
	      LOG (2, "equivalence class of %d is frozen", repr);
	      assert (lglifrozen (lgl, repr));
	    }
	  } else mindfsimap[ulit] = mindfsi;
	}
      }
    }
  }
DONE:
  lglrelstk (lgl, &stk);
  lglrelstk (lgl, &component);
  DEL (mindfsimap, 2*lgl->nvars);
  DEL (dfsimap, 2*lgl->nvars);
  if (!res) DEL (lgl->repr, lgl->nvars);
  lglstop (lgl);
  return res;
}

static int64_t lglsteps (LGL * lgl) {
  int64_t steps = lgl->stats.props.simp;
  steps += lgl->stats.props.search;
  steps += lgl->stats.trd.steps;
  steps += lgl->stats.unhd.steps;
  steps += lgl->stats.elm.steps;
  return steps;
}

static int lglterminate (LGL * lgl) {
  int64_t steps;
  int res;
  if (!lgl->term.fun) return 0;
  if (lgl->term.done) return 1;
  steps = lglsteps (lgl);
  if (steps < lgl->limits.term.steps) return 0;
  res = lgl->term.fun (lgl->term.state);
  if (res) lgl->term.done = res;
  else lgl->limits.term.steps = steps + lgl->opts.termint.val;
  return  res;
}

static int lglsyncunits (LGL * lgl) {
  int * units, * eou, * p, elit, erepr, ilit, res, count = 0;
  void (*produce)(void*, int);
  int64_t steps;
  Ext * ext;
  Val val;
  assert (!lgl->simplifying || !lgl->level);
  if (!lgl->units.consume.fun) return 1;
  steps = lglsteps (lgl);
  if (steps < lgl->limits.sync.steps) return 1;
  lgl->limits.sync.steps = steps + lgl->opts.syncint.val;
  lgl->units.consume.fun (lgl->units.consume.state, &units, &eou);
  if (units == eou) return 1;
  produce = lgl->units.produce.fun;
  lgl->units.produce.fun = 0;
  for (p = units; !lgl->mt && p < eou; p++) {
    elit = *p;
    erepr = lglerepr (lgl, elit);
    ext = lglelit2ext (lgl, erepr);
    assert (!ext->equiv);
    ilit = ext->repr;
    if (!ilit) continue;
    if (erepr < 0) ilit = -ilit;
    if (ilit == 1) continue;
    if (ilit == -1) val = -1;
    else {
      assert (abs (ilit) > 1);
      val = lglval (lgl, ilit);
      if (val && lglevel (lgl, ilit)) val = 0;
    }
    if (val == 1) continue;
    if (val == -1) {
      LOG (1, "mismatching synchronized external unit %d", elit);
      if (lgl->level > 0) lglbacktrack (lgl, 0);
      lgl->mt = 1;
    } else if (!lglisfree (lgl, ilit)) continue;
    else {
      assert (!val);
      if (lgl->level > 0) lglbacktrack (lgl, 0);
      lglunit (lgl, ilit);
      LOG (2, "importing internal unit %d external %d",
	   lgl->tid, ilit, elit);
      count++;
    }
  }
  lgl->units.produce.fun = produce;
  if (lgl->units.consumed.fun) 
    lgl->units.consumed.fun (lgl->units.consumed.state, count);
  if (lgl->mt) return 0;
  if (count)
    LOG (1, "imported %d units", lgl->tid, count);
  if (!count) return 1;
  assert (!lgl->level);
  if (lgl->distilling) { assert (!lgl->propred); lgl->propred = 1; }
  res = lglbcp (lgl);
  if (lgl->distilling) { assert (lgl->propred); lgl->propred = 0; }
  if(!res && !lgl->mt) lgl->mt = 1;
  return res;
}

static int lglprbpull (LGL * lgl, int lit, int probe) {
  AVar * av;
  assert (lgl->level == 1);
  av = lglavar (lgl, lit);
  if (av->mark) return 0;
  if (!lglevel (lgl, lit)) return 0;
  assert (lglevel (lgl, lit) == 1);
  av->mark = 1;
  lglpushstk (lgl, &lgl->seen, -lit);
  LOG (3, "pulled in literal %d during probing analysis", -lit);
  return 1;
}

static int lglprbana (LGL * lgl, int probe) {
  int open, lit, r0, r1, tag, red, other, res, * p, * rsn;
  assert (lgl->level == 1);
  assert (lgl->conf.lit);
  assert (lglmtstk (&lgl->seen));
  res = open = 0;
  lit = lgl->conf.lit;
  r0 = lgl->conf.rsn[0], r1 = lgl->conf.rsn[1];
  open = lglprbpull (lgl, lit, probe);
  LOG (2, "starting probing analysis with reason of literal %d", lit);
  for (;;) {
    assert (lglevel (lgl, lit) == 1);
    tag = r0 & MASKCS;
    if (tag == BINCS || tag == TRNCS) {
      other = r0 >> RMSHFT;
      if (lglprbpull (lgl, other, probe)) open++;
      if (tag == TRNCS && lglprbpull (lgl, r1, probe)) open++;
    } else {
      assert (tag==LRGCS);
      red = r0 & REDCS;
      p = lglidx2lits (lgl, red, r1);
      while ((other = *p++)) open += lglprbpull (lgl, other, probe);
    }
    LOG (3, "open %d antecedents in probing analysis", open-1);
    assert (open > 0);
    while (!lglmarked (lgl, lit = lglpopstk (&lgl->trail)))
      lglunassign (lgl, lit);
    lglunassign (lgl, lit);
    if (!--open) { res = lit; break; }
    LOG (2, "analyzing reason of literal %d in probing analysis next", lit);
    rsn = lglrsn (lgl, lit);
    r0 = rsn[0], r1 = rsn[1];
  }
  assert (res);
  if (res == probe)
    LOG (2, "probing analysis returns the probe %d as 1st UIP");
  else
    LOG (2, "probing analysis returns different 1st UIP %d and not probe %d",
         res, probe);
  lglpopnunmarkstk (lgl, &lgl->seen);
  return res;
}

static int lglideref (LGL * lgl, int elit) {
  int ilit, res, repr;
  Ext * ext;
  if (abs (elit) > lgl->maxext) return -1;
  repr = lglerepr (lgl, elit);
  ext = lglelit2ext (lgl, repr);
  assert (!ext->equiv);
  res = ext->val;
  if (!res) {
    ilit = ext->repr;
    res = ilit ? lglcval (lgl, ilit) : 0;
  }
  if (repr < 0) res = -res;
  return res;
}

static int lglmyturn (LGL * lgl, int counts) {
  return 1;
  if (lgl->tid < 0) return 1;
  assert (lgl->tid < lgl->tids);
  return (counts % lgl->tids) == lgl->tid;
}

static int lglprobe (LGL * lgl) {
  int lit, root, units, lifted, ok, old, orig, first, dom;
  int nprobes, nvars, probed, fixed, changed, success = 0;
  int idx;
  Stk probes, lift, saved;
  unsigned pos, delta;
  const int * p;
  int64_t limit;
  Val val;
#if 0 && !defined(NLGLPICOSAT)
  int oldpicosatchk = lgl->picosat.chk;
#endif
  if (!lgl->nvars) return 1;
  if (!lgl->opts.probe.val) return 1;
  lgl->stats.prb.count++;
  lglstart (lgl, &lgl->stats.tms.prb);
  assert (!lgl->simp);
  lgl->simp = 1;
  if (lgl->level > 0) lglbacktrack (lgl, 0);
  assert (lgl->measureagility);
  lgl->measureagility = 0;
  assert (!lgl->probing);
  lgl->probing = 1;
#if 0 && !defined(NLGLPICOSAT)
  oldpicosatchk = lgl->picosat.chk;
  lgl->picosat.chk = 0;
#endif
  CLR (lift); CLR (probes); CLR (saved);
  for (idx = 2; idx < lgl->nvars; idx++) {
    if (!lglisfree (lgl, idx)) continue;
    LOG (1, "new probe %d", idx);
    lglpushstk (lgl, &probes, idx);
  }
  nprobes = lglcntstk (&probes);
  nvars = lgl->nvars - 1;
  LOG (1, "found %d active probes out of %d variables %.1f%%",
       nprobes, nvars, lglpcnt (nprobes, nvars));
  lifted = units = 0;
  probed = 0;
  orig = lglcntstk (&lgl->trail);
  if (!nprobes) goto DONE;
  pos = lglrand (lgl) % nprobes;
  delta = lglrand (lgl) % nprobes;
  if (!delta) delta++;
  while (lglgcd (delta, nprobes) > 1)
    if (++delta == nprobes) delta = 1;
  LOG (1, "probing start %u delta %u mod %u", pos, delta, nprobes);
  if (lgl->stats.prb.count == 1) limit = lgl->opts.prbmaxeff.val/10;
  else limit = (lgl->opts.prbreleff.val*lgl->stats.visits.search)/1000;
  if (limit < lgl->opts.prbmineff.val) limit = lgl->opts.prbmineff.val;
  if (limit > lgl->opts.prbmaxeff.val) limit = lgl->opts.prbmaxeff.val;
  LOG (2, "probing with penalty %d", lgl->limits.prb.pen);
  if (lgl->limits.prb.pen < 0) limit <<= -lgl->limits.prb.pen;
  if (lgl->limits.prb.pen > 0) limit >>= lgl->limits.prb.pen;
  LOG (2, "probing with up to %lld propagations", (long long) limit);
  limit += lgl->stats.visits.simp;
  changed = first = 0;
  for (;;) {
    if (lgl->stats.visits.simp >= limit) break;
    if (lglterminate (lgl)) break;
    if (!lglsyncunits (lgl)) break;
    assert (pos < (unsigned) nprobes);
    root = probes.start[pos];
    if (root == first) {
       if (changed) changed = 0; else break;
    }
    if (!first) first = root;
    pos += delta;
    if (pos >= nprobes) pos -= nprobes;
    if (lglval (lgl, root)) continue;
    lgl->stats.prb.probed++;
    probed++;
    lglclnstk (&lift);
    lglclnstk (&saved);
    LOG (2, "next probe %d positive phase", root);
    assert (!lgl->level);
    lgliassume (lgl, root);
    old = lglcntstk (&lgl->trail);
    ok = lglbcp (lgl);
    dom = 0;
    if (ok) {
      lglclnstk (&saved);
      for (p = lgl->trail.start + old; p < lgl->trail.top; p++)
	lglpushstk (lgl, &saved, *p);
    } else dom = lglprbana (lgl, root);
    lglbacktrack (lgl, 0);
    if (!ok) {
      LOG (1, "failed literal %d on probing", dom, root);
      lglpushstk (lgl, &lift, -dom);
      goto MERGE;
    }
    LOG (2, "next probe %d negative phase", -root);
    assert (!lgl->level);
    lgliassume (lgl, -root);
    ok = lglbcp (lgl);
    if (ok) {
      for (p = saved.start; p < saved.top; p++) {
	lit = *p;
	val = lglval (lgl, lit);
	if (val <= 0) continue;
	lifted++;
	lgl->stats.prb.lifted++;
	lglpushstk (lgl, &lift, lit);
	LOG (2, "lifted %d", lit);
      }
    } else dom = lglprbana (lgl, -root);
    lglbacktrack (lgl, 0);
    if (!ok) {
      LOG (1, "failed literal %d on probing %d", dom, -root);
      lglpushstk (lgl, &lift, -dom);
    }
MERGE:
    while (!lglmtstk (&lift)) {
      lit = lglpopstk (&lift);
      val = lglval (lgl, lit);
      if (val > 0) continue;
      if (val < 0) goto EMPTY;
      lglunit (lgl, lit);
      success = changed = 1;
      units++;
      lgl->stats.prb.failed++;
      if (lglbcp (lgl)) continue;
EMPTY:
      LOG (1, "empty clause after propagating lifted and failed literals");
      lgl->mt = 1;
      goto DONE;
    }
  }
DONE:
  LOG (1, "%ssuccessfully probed %d out of %d probes %.1f%%",
       success ? "" : "un", probed, nprobes, lglpcnt (probed, nprobes));
  lglrelstk (lgl, &lift);
  lglrelstk (lgl, &probes);
  lglrelstk (lgl, &saved);
  fixed = lglcntstk (&lgl->trail) - orig;
  LOG (1, "found %d units %.1f%% lifted %d through probing",
       units, lglpcnt (units, probed), lifted);
  lgl->measureagility = 1;
  assert (lgl->probing);
  lgl->probing = 0;
#if 0 && !defined(NLGLPICOSAT)
  assert (!lgl->picosat.chk);
  lgl->picosat.chk = oldpicosatchk;
#endif
  assert (lgl->simp);
  lgl->simp = 0;
  lglrep (lgl, 1, 'p');
  if (success && lgl->limits.prb.pen > MINPEN) lgl->limits.prb.pen--;
  if (!success && lgl->limits.prb.pen < MAXPEN) lgl->limits.prb.pen++;
  lglstop (lgl);
  lgl->limits.prb.cinc += lgl->opts.prbcintinc.val;
  lgl->limits.prb.vinc += lgl->opts.prbvintinc.val;
  lgl->limits.prb.visits = lgl->stats.visits.search + lgl->limits.prb.vinc;
  lgl->limits.prb.confs = lgl->stats.confs + lgl->limits.prb.cinc;
  lgl->limits.prb.prgss = lgl->stats.prgss;
  lgl->limits.prb.irr = lgl->stats.irr + lgl->opts.prbirrintinc.val;
  return !lgl->mt;
}

static int lglsmall (LGL * lgl) {
  int maxirrlidx = lglcntstk (&lgl->irr);
  if (maxirrlidx > MAXIRRLIDX) return 0;
  return  1;
}

static void lgldense (LGL * lgl) {
  int lit, lidx, count, idx, other, other2, blit, sign, tag, red;
  const int * start, * top, * c, * p, * eow;
  int * q, * w;
  EVar * ev;
  HTS * hts;
  assert (!lgl->dense);
  assert (!lgl->evars);
  assert (lglsmall (lgl));
  assert (lglmtstk (&lgl->esched));
  assert (!lgl->elm.pivot);
  count = 0;
  other2 = 0;
  NEW (lgl->evars, lgl->nvars);
  for (idx = 2; idx < lgl->nvars; idx++) {
    ev = lgl->evars + idx;
    ev->pos = -1;
  }
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = lglhts (lgl, lit);
      if (!hts->count) continue;
      q = w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (tag == LRGCS) continue;
	red = blit & REDCS;
	*q++ = blit;
	assert (tag != LRGCS);
	if (tag == TRNCS) *q++ = *p;
	if (red) continue;
	other = blit >> RMSHFT;
	if (abs (other) < idx) continue;
	if (tag == TRNCS) {
	  other2 = *p;
	  if (abs (other2) < idx) continue;
	}
	lglincocc (lgl, lit), count++;
	lglincocc (lgl, other), count++;
	if (tag == BINCS) continue;
	assert (tag == TRNCS);
	lglincocc (lgl, other2), count++;
      }
      lglshrinkhts (lgl, hts, q - w);
    }
  if (count)
    LOG (1, "counted %d occurrences in small irredundant clauses", count);
  count = 0;
  start = lgl->irr.start;
  top = lgl->irr.top;
  for (c = start; c < top; c = p + 1) {
    p = c;
    if (*c >= NOTALIT) continue;
    lidx = c - start;
    assert (lidx < MAXIRRLIDX);
    blit = (lidx << RMSHFT) | IRRCS;
    for (; (lit = *p); p++) {
      hts = lglhts (lgl, lit);
      lglpushwch (lgl, hts, blit);
      lglincocc (lgl, lit), count++;
    }
  }
  if (count)
    LOG (1, "counted %d occurrences in large irredundant clauses", count);
  count = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    ev = lglevar (lgl, idx);
    if (ev->pos >= 0) continue;
    if (lglifrozen (lgl, idx)) continue;
    assert (!ev->score && !ev->occ[0] && !ev->occ[1]);
    lglesched (lgl, idx);
    count++;
  }
  if (count) LOG (1, "scheduled %d zombies", count);
  lgl->dense = 1;
}

static void lglsparse (LGL * lgl) {
  int idx, sign, lit, count, blit, tag;
  int * w, *p, * eow, * q;
  HTS * hts;
  assert (lgl->dense);
  count = 0;
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = lglhts (lgl, lit);
      if (!hts->count) continue;
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = q = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == IRRCS) { count++; continue; }
	*q++ = blit;
	if (tag == BINCS) continue;
	assert (tag == LRGCS || tag == TRNCS);
	*q++ = *++p;
      }
      assert (hts->count - (p - q) == q - w);
      lglshrinkhts (lgl, hts, q - w);
    }
  DEL (lgl->evars, lgl->nvars);
  lglrelstk (lgl, &lgl->esched);
  LOG (1, "removed %d full irredundant occurrences", count);
  lgl->dense = 0;
}

static int lglm2i (LGL * lgl, int mlit) {
  int res, midx = abs (mlit);
  assert (0 < midx);
  res = lglpeek (&lgl->elm.m2i, midx);
  if (mlit < 0) res = -res;
  return res;
}

static int lgli2m (LGL * lgl, int ilit) {
  AVar * av = lglavar (lgl, ilit);
  int res = av->mark;
  if (!res) {
    res = lglcntstk (&lgl->seen) + 1;
    av->mark = res;
    assert (2*lglcntstk (&lgl->seen) == lglcntstk (&lgl->elm.lsigs) - 2);
    assert (2*lglcntstk (&lgl->seen) == lglcntstk (&lgl->elm.noccs) - 2);
    assert (2*lglcntstk (&lgl->seen) == lglcntstk (&lgl->elm.mark) - 2);
    assert (2*lglcntstk (&lgl->seen) == lglcntstk (&lgl->elm.occs) - 2);
    assert (lglcntstk (&lgl->seen) == lglcntstk (&lgl->elm.m2i) - 1);
    lglpushstk (lgl, &lgl->seen, abs (ilit));
    lglpushstk (lgl, &lgl->elm.lsigs, 0);
    lglpushstk (lgl, &lgl->elm.lsigs, 0);
    lglpushstk (lgl, &lgl->elm.noccs, 0);
    lglpushstk (lgl, &lgl->elm.noccs, 0);
    lglpushstk (lgl, &lgl->elm.mark, 0);
    lglpushstk (lgl, &lgl->elm.mark, 0);
    lglpushstk (lgl, &lgl->elm.occs, 0);
    lglpushstk (lgl, &lgl->elm.occs, 0);
    lglpushstk (lgl, &lgl->elm.m2i, abs (ilit));
    LOG (4, "mapped internal variable %d to marked variable %d",
         abs (ilit), res);
  }
  if (ilit < 0) res = -res;
  return res;
}

static unsigned lglsig (int lit) {
  unsigned ulit = lglulit (lit), res;
  assert (ulit >= 2);
  ulit -= 2;
  res = (1u << (ulit & 31));
  return res;
}

static void lgladdecl (LGL * lgl, const int * c) {
  int ilit, mlit, umlit, size = 0, lidx, next, prev;
  unsigned csig = 0;
  const int * p;
  Val val;
  LOGCLS (3, c, "copying irredundant clause");
  lgl->stats.elm.steps++;
  lgl->stats.elm.copies++;
  size = 0;
  for (p = c; (ilit = *p); p++) {
    val = lglval (lgl, ilit);
    assert (val <= 0);
    if (val < 0) continue;
    size++;
    if (abs (ilit) == lgl->elm.pivot) continue;
    mlit = lgli2m (lgl, ilit);
    assert (abs (mlit) != 1);
    csig |= lglsig (mlit);
  }
  assert (size >= 1);
  lidx = next = lglcntstk (&lgl->elm.lits);
  assert (next > 0);
  for (p = c; (ilit = *p); p++) {
    val = lglval (lgl, ilit);
    if (val < 0) continue;
    mlit = lgli2m (lgl, ilit);
    lglpushstk (lgl, &lgl->elm.lits, mlit);
    umlit = lglulit (mlit);
    prev = lglpeek (&lgl->elm.occs, umlit);
    lglpushstk (lgl, &lgl->elm.next, prev);
    lglpoke (&lgl->elm.occs, umlit, next++);
    lglpushstk (lgl, &lgl->elm.csigs, csig);
    lglpushstk (lgl, &lgl->elm.sizes, size);
    lgl->elm.noccs.start[umlit]++;
    lgl->elm.lsigs.start[umlit] |= csig;
  }
  lglpushstk (lgl, &lgl->elm.lits, 0);
  lglpushstk (lgl, &lgl->elm.next, 0);
  lglpushstk (lgl, &lgl->elm.csigs, 0);
  lglpushstk (lgl, &lgl->elm.sizes, 0);
  lgl->elm.necls++;
  LOGCLS (4, lgl->elm.lits.start + lidx, "copied and mapped clause");
#ifndef NDEBUG
  LOGMCLS (4, lgl->elm.lits.start + lidx, "copied and remapped clause");
  {
    int i, j = 0;
    for (i = 0; c[i]; i++) {
      Val val = lglval (lgl, c[i]);
      assert (val <= 0);
      if (val < 0) continue;
      assert (c[i] == lglm2i (lgl, lglpeek (&lgl->elm.lits, lidx + j++)));
    }
  }
#endif
}

static int lglecls (LGL * lgl, int lit) {
  int blit, tag, red, other, lidx, count;
  const int * p, * w, * eow, * c;
  int d[4];
  HTS * hts;
  LOG (3, "copying irredundant clauses with %d", lit);
  count = 0;
  hts = lglhts (lgl, lit);
  if (!hts->count) return 0;
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    red = blit & REDCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (red) continue;
    if (tag == BINCS || tag == TRNCS) {
      d[0] = lit;
      other = blit >> RMSHFT;
      d[1] = other;
      if (tag == TRNCS) d[2] = *p, d[3] = 0;
      else d[2] = 0;
      c = d;
    } else {
      assert (tag == IRRCS);
      lidx = (tag == IRRCS) ? (blit >> RMSHFT) : *p;
      c = lglidx2lits (lgl, 0, lidx);
    }
    lgladdecl (lgl, c);
    count++;
  }
  return count;
}

static void lglrstecls (LGL * lgl)  {
  assert (lgl->elm.pivot);
  lglclnstk (&lgl->elm.lits);
  lglclnstk (&lgl->elm.next);
  lglclnstk (&lgl->elm.csigs);
  lglclnstk (&lgl->elm.lsigs);
  lglclnstk (&lgl->elm.sizes);
  lglclnstk (&lgl->elm.occs);
  lglclnstk (&lgl->elm.noccs);
  lglclnstk (&lgl->elm.mark);
  lglclnstk (&lgl->elm.m2i);
  lglpopnunmarkstk (lgl, &lgl->seen);
  lgl->elm.pivot = 0;
}

static void lglrelecls (LGL * lgl)  {
  lglrelstk (lgl, &lgl->elm.lits);
  lglrelstk (lgl, &lgl->elm.next);
  lglrelstk (lgl, &lgl->elm.csigs);
  lglrelstk (lgl, &lgl->elm.lsigs);
  lglrelstk (lgl, &lgl->elm.sizes);
  lglrelstk (lgl, &lgl->elm.occs);
  lglrelstk (lgl, &lgl->elm.noccs);
  lglrelstk (lgl, &lgl->elm.mark);
  lglrelstk (lgl, &lgl->elm.m2i);
  lglrelstk (lgl, &lgl->clv);
}

static int lgl2manyoccs4elm (LGL * lgl, int lit) {
  return lglhts (lgl, lit)->count > lgl->opts.elmocclim.val;
}

static int lglchkoccs4elmlit (LGL * lgl, int lit) {
  int blit, tag, red, other, other2, lidx, size;
  const int * p, * w, * eow, * c, * l;
  HTS * hts;
  hts = lglhts (lgl, lit);
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    red = blit & REDCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (red) continue;
    if (tag == BINCS || tag == TRNCS) {
      other = blit >> RMSHFT;
      if (lgl2manyoccs4elm (lgl, other)) return 0;
      if (tag == TRNCS) {
	other2 = *p;
	if (lgl2manyoccs4elm (lgl, other2)) return 0;
      }
    } else {
      assert (tag == IRRCS);
      lidx = blit >> RMSHFT;
      c = lglidx2lits (lgl, 0, lidx);
      size = 0;
      for (l = c; (other = *l); l++) {
	if (lgl2manyoccs4elm (lgl, other)) return 0;
	if (++size > lgl->opts.elmclslim.val) return 0;
      }
    }
  }
  return 1;
}

static int lglchkoccs4elm (LGL * lgl, int idx) {
  if (lgl2manyoccs4elm (lgl, idx)) return 0;
  if (lgl2manyoccs4elm (lgl, -idx)) return 0;
  if (!lglchkoccs4elmlit (lgl, idx)) return 0;
  return lglchkoccs4elmlit (lgl, -idx);
}

static void lglinitecls (LGL * lgl, int idx) {
  int clauses;
  assert (!lgl->elm.pivot);
  assert (idx >= 2);
  assert (lglmtstk (&lgl->elm.lits));
  assert (lglmtstk (&lgl->elm.next));
  assert (lglmtstk (&lgl->elm.csigs));
  assert (lglmtstk (&lgl->elm.lsigs));
  assert (lglmtstk (&lgl->elm.sizes));
  assert (lglmtstk (&lgl->elm.occs));
  assert (lglmtstk (&lgl->elm.noccs));
  assert (lglmtstk (&lgl->elm.m2i));
  assert (lglmtstk (&lgl->seen));
  lgl->elm.pivot = idx;
  lglpushstk (lgl, &lgl->elm.mark, 0);
  lglpushstk (lgl, &lgl->elm.mark, 0);
  lglpushstk (lgl, &lgl->elm.occs, 0);
  lglpushstk (lgl, &lgl->elm.occs, 0);
  lglpushstk (lgl, &lgl->elm.noccs, 0);
  lglpushstk (lgl, &lgl->elm.noccs, 0);
  lglpushstk (lgl, &lgl->elm.lsigs, 0);
  lglpushstk (lgl, &lgl->elm.lsigs, 0);
  lglpushstk (lgl, &lgl->elm.m2i, 0);
  (void) lgli2m (lgl, idx);
  lglpushstk (lgl, &lgl->elm.lits, 0);
  lglpushstk (lgl, &lgl->elm.next, 0);
  lglpushstk (lgl, &lgl->elm.csigs, 0);
  lglpushstk (lgl, &lgl->elm.sizes, 0);
  lgl->elm.necls = 0;
  clauses = lglecls (lgl, idx);
  lgl->elm.negcls = lgl->elm.necls;
  lgl->elm.neglidx = lglcntstk (&lgl->elm.lits);
  clauses += lglecls (lgl, -idx);
  LOG (2, "found %d variables in %d clauses with %d or %d",
       lglcntstk (&lgl->seen), clauses, idx, -idx);
  assert (lgl->elm.pivot);
}

static void lglelrmcls (LGL * lgl, int lit, int * c, int clidx) {
  int lidx, i, other, ulit, * lits, * csigs, blit, tag, red, other2, size;
  int * p, * eow, * w, count;
  HTS * hts;
  lits = lgl->elm.lits.start;
  csigs = lgl->elm.csigs.start;
  assert (lits < c && c < lgl->elm.lits.top - 1);
  lidx = c - lits;
  LOGCLS (2, c, "removing clause");
  for (i = lidx; (other = lits[i]); i++) {
    assert (other < NOTALIT);
    lits[i] = REMOVED;
    csigs[i] = 0;
    ulit = lglulit (other);
    assert (ulit < lglcntstk (&lgl->elm.noccs));
    assert (lgl->elm.noccs.start[ulit] > 0);
    lgl->elm.noccs.start[ulit] -= 1;
  }
  size = lglpeek (&lgl->elm.sizes, lidx);
  hts = lglhts (lgl, lit);
  assert (hts->count > 0 && hts->count >= clidx);
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  blit = tag = count = 0;
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    red = blit & REDCS;
    if (red) continue;
    if (count == clidx) break;
    count++;
  }
  assert (count == clidx);
  assert (blit && tag);
  assert (p < eow);
  if (tag == BINCS) {
    assert (size >= 2);
    other = blit >> RMSHFT;
    lglrmbcls (lgl, lit, other, 0);
  } else if (tag == TRNCS) {
    other = blit >> RMSHFT;
    other2 = *p;
    lglrmtcls (lgl, lit, other, other2, 0);
  } else {
    assert (tag == IRRCS || tag == LRGCS);
    lidx = (tag == IRRCS) ? (blit >> RMSHFT) : *p;
#ifndef NDEBUG
    {
      int * q, * d = lglidx2lits (lgl, 0, lidx);
      for (q = d; *q; q++)
	;
      assert (q - d >= size);
    }
#endif
    lglrmlcls (lgl, lidx, 0);
  }
}

static int lglbacksub (LGL * lgl, int * c, int str) {
  int * start = lgl->elm.lits.start, * p, * q, marked = 0, res, * d;
  int lit, ulit, occ, next, osize, other, uolit, size, plit, phase, clidx;
  unsigned ocsig, lsig, csig = 0;
#ifndef NLGLOG
  const char * mode = str ? "strengthening" : "subsumption";
#endif
  LOGMCLS (3, c, "backward %s check for clause", mode);
  LOGCLS (3, c, "backward %s check for mapped clause", mode);
  assert (!str || lglstr (lgl));
  phase = (c - start) >= lgl->elm.neglidx;
  for (p = c; (lit = *p); p++)
    if (abs (lit) != 1)
      csig |= lglsig (lit);
  size = p - c;
  assert (csig == lglpeek (&lgl->elm.csigs, c - start));
  assert (size == lglpeek (&lgl->elm.sizes, c - start));
  res = 0;

  if (str) phase = !phase;
  lit = phase ? -1 : 1;

  ulit = lglulit (lit);
  occ = lglpeek (&lgl->elm.noccs, ulit);
  if (!str && occ <= 1) return 0;
  if (str && !occ) return 0;
  lsig = lglpeek (&lgl->elm.lsigs, ulit);
  if ((csig & ~lsig)) return 0;
  for (next = lglpeek (&lgl->elm.occs, ulit);
       !res && next;
       next = lglpeek (&lgl->elm.next, next)) {
      if (next == p - start) continue;
      if (phase != (next >= lgl->elm.neglidx)) continue;
      plit = lglpeek (&lgl->elm.lits, next);
      if (plit >= NOTALIT) continue;
      assert (plit == lit);
      osize = lglpeek (&lgl->elm.sizes, next);
      if (osize > size) continue;
      ocsig = lglpeek (&lgl->elm.csigs, next);
      assert (ocsig);
      if ((ocsig & ~csig)) continue;
      if (!marked) {
	for (q = c; (other = *q); q++) {
	  if (str && abs (other) == 1) other = -other;
	  uolit = lglulit (other);
	  assert (!lglpeek (&lgl->elm.mark, uolit));
	  lglpoke (&lgl->elm.mark, uolit, 1);
	}
	marked = 1;
      }
      d = lgl->elm.lits.start + next;
      if (c <= d && d < c + size) continue;
      lgl->stats.elm.steps++;
      if (str) lgl->stats.elm.strchks++; else lgl->stats.elm.subchks++;
      while (d[-1]) d--;
      assert (c != d);
      LOGMCLS (3, d, "backward %s check with clause", mode);
      res = 1;
      for (q = d; res && (other = *q); q++) {
	uolit = lglulit (other);
	res = lglpeek (&lgl->elm.mark, uolit);
      }
      if (!res || !str || osize < size) continue;
      LOGMCLS (2, d, "strengthening by double self-subsuming resolution");
      assert ((c - start) < lgl->elm.neglidx);
      assert ((d - start) >= lgl->elm.neglidx);
      assert (phase);
      clidx = 0;
      q = lgl->elm.lits.start + lgl->elm.neglidx;
      while (q < d) {
	other = *q++;
	if (other >= NOTALIT) { while (*q++) ; continue; }
	if (!other) clidx++;
      }
      LOGMCLS (2, d,
	"strengthened and subsumed original irredundant clause");
      LOGCLS (3, d, "strengthened and subsumed mapped irredundant clause");
      lglelrmcls (lgl, -lgl->elm.pivot, d, clidx);
  }
  if (marked) {
    for (p = c; (lit = *p); p++) {
      if (str && abs (lit) == 1) lit = -lit;
      ulit = lglulit (lit);
      assert (lglpeek (&lgl->elm.mark, ulit));
      lglpoke (&lgl->elm.mark, ulit, 0);
    }
  }
  return res;
}

static void lglelmsub (LGL * lgl) {
  int clidx, count, subsumed, pivot, * c;
  count = clidx = subsumed = 0;
  pivot = lgl->elm.pivot;
  for (c = lgl->elm.lits.start + 1;
       c < lgl->elm.lits.top &&
         lgl->limits.elm.steps > lgl->stats.elm.steps;
       c++) {
    if (count++ == lgl->elm.negcls) clidx = 0, pivot = -pivot;
    if (lglbacksub (lgl, c, 0)) {
      subsumed++;
      lgl->stats.elm.sub++;
      LOGMCLS (2, c, "subsumed original irredundant clause");
      LOGCLS (3, c, "subsumed mapped irredundant clause");
      lglelrmcls (lgl, pivot, c, clidx);
    } else clidx++;
    while (*c) c++;
  }
  LOG (2, "subsumed %d clauses containing %d or %d",
       subsumed, lgl->elm.pivot, -lgl->elm.pivot);
}

static int lglelmstr (LGL * lgl) {
  int clidx, count, strengthened, pivot, * c, * p, mlit, ilit, res, found;
  int size;
  count = clidx = strengthened = 0;
  pivot = lgl->elm.pivot;
  res = 0;
  LOG (3, "strengthening with pivot %d", pivot);
  for (c = lgl->elm.lits.start + 1;
       c < lgl->elm.lits.top &&
         lgl->limits.elm.steps > lgl->stats.elm.steps;
       c++) {
    if (count++ == lgl->elm.negcls) {
      clidx = 0, pivot = -pivot;
      LOG (3, "strengthening with pivot %d", pivot);
    }
    if (*c == REMOVED) {
      while (*c) { assert (*c == REMOVED); c++; }
      continue;
    }
    if (lglbacksub (lgl, c, 1)) {
      strengthened++;
      lgl->stats.elm.str++;
      LOGMCLS (2, c, "strengthening original irredundant clause");
      LOGCLS (3, c, "strengthening mapped irredundant clause");
      assert (lglmtstk (&lgl->clause));
      found = 0;
      size = 0;
      for (p = c; (mlit = *p); p++) {
	ilit = lglm2i (lgl, *p);
	if (ilit == pivot) { found = 1; continue; }
	assert (!lglval (lgl, ilit));
	lglpushstk (lgl, &lgl->clause, ilit);
	size++;
      }
      assert (found);
      lglpushstk (lgl, &lgl->clause, 0);
      LOGCLS (2, lgl->clause.start, "static strengthened irredundant clause");
#ifndef NLGLPICOSAT
      lglpicosatchkclsaux (lgl, lgl->clause.start);
#endif
      lglelrmcls (lgl, pivot, c, clidx);
      lgladdcls (lgl, 0, 0);
      lglclnstk (&lgl->clause);
      if (size == 1) { res = 1; break; }
    } else clidx++;
    while (*c) c++;
  }
  LOG (2, "strengthened %d clauses containing %d or %d",
       strengthened, lgl->elm.pivot, -lgl->elm.pivot);
  return res;
}

static void lglflushlit (LGL * lgl, int lit) {
  int blit, tag, red, other, other2, lidx, count;
  const int * p, * w, * eow;
  int * c, * q;
  HTS * hts;
  assert (lgl->dense);
  hts = lglhts (lgl, lit);
  if (!hts->count) return;
  LOG (2, "flushing positive occurrences of %d", lit);
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  count = 0;
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    red = blit & REDCS;
    other = blit >> RMSHFT;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (!red && tag == LRGCS) continue;
    if (!red) assert (lgl->stats.irr > 0), lgl->stats.irr--;
    if (tag == BINCS) {
      lglrmbwch (lgl, other, lit, red);
      if (red) assert (lgl->stats.red.bin > 0), lgl->stats.red.bin--;
      else lgldecocc (lgl, other);
      LOG (2, "flushed %s binary clause %d %d", lglred2str (red), lit, other);
      count++;
    } else if (tag == TRNCS) {
      other2 = *p;
      lglrmtwch (lgl, other2, lit, other, red);
      lglrmtwch (lgl, other, lit, other2, red);
      if (red) assert (lgl->stats.red.trn > 0), lgl->stats.red.trn--;
      else lgldecocc (lgl, other), lgldecocc (lgl, other2);
      LOG (2, "flushed %s ternary clause %d %d %d",
           lglred2str (red), lit, other, other2);
      count++;
    } else {
      assert (!red);
      assert (tag == IRRCS || tag == LRGCS);
      lidx = (tag == IRRCS) ? other : *p;
      c = lglidx2lits (lgl, red, lidx);
      LOGCLS (2, c, "flushed irredundant large clause");
      for (q = c; (other = *q); q++) {
	*q = REMOVED;
	if (red) continue;
	lgldecocc (lgl, other);
	if (other == lit) continue;
	lglrmlocc (lgl, other, lidx);
      }
      *q = REMOVED;
      count++;
    }
  }
  lglshrinkhts (lgl, hts, 0);
  LOG (2, "flushed %d clauses in which %d occurs", count, lit);
}

static int lglflush (LGL * lgl) {
  int lit, count;
  if (lgl->mt) return 0;
  assert (!lgl->level && lgl->dense);
  if (lgl->flushed == lglcntstk (&lgl->trail)) return 1;
  if (!lglbcp (lgl)) { lgl->mt = 1; return 0; }
  if (!lglsyncunits (lgl)) { assert (lgl->mt); return 0; }
  count = 0;
  while  (lgl->flushed < lglcntstk (&lgl->trail)) {
    lit = lglpeek (&lgl->trail, lgl->flushed++);
    lglflushlit (lgl, lit);
    count++;
  }
  LOG (2, "flushed %d literals", count);
  assert (!lgl->mt);
  return 1;
}

static void lglepush (LGL * lgl, int ilit) {
  int elit = ilit ? lglexport (lgl, ilit) : 0;
  lglpushstk (lgl, &lgl->extend, elit);
  LOG (4, "pushing external %d internal %d", elit, ilit);
}

static void lglelmfrelit (LGL * lgl, int mpivot,
			  int * sop, int * eop, int * son, int * eon,
			  int bintoo) {
  int ipivot = mpivot * lgl->elm.pivot, clidx, ilit, tmp, cover, maxcover;
  int * c, * d, * e, * p, * q, lit, nontrivial, idx, sgn, clen, reslen;
  EVar * ev;
  int size;
  assert (mpivot == 1 || mpivot == -1);
  assert (ipivot);
  LOG (3,
       "blocked clause elimination and forced resolution of clauses with %d",
        ipivot);
  clidx = 0;
  ev = lglevar (lgl, ipivot);
  cover = lglpeek (&lgl->elm.noccs, lglulit (-mpivot));
  for (c = sop; c < eop; c = p + 1) {
    if (*c == REMOVED) { for (p = c + 1; *p; p++) ; continue; }
    maxcover = 0;
    for (p = c; (lit = *p); p++) {
      if (lit == mpivot) continue;
      assert (lit != -mpivot);
      maxcover += lglpeek (&lgl->elm.noccs, lglulit (-lit));
    }
    if (maxcover < cover - 1) { clidx++; continue; }
    for (p = c; (lit = *p); p++) {
      if (lit == mpivot) continue;
      assert (lit != -mpivot);
      idx = abs (lit);
      assert (!lglpeek (&lgl->elm.mark, idx));
      sgn = lglsgn (lit);
      lglpoke (&lgl->elm.mark, idx, sgn);
    }
    nontrivial = 0;
    clen = p - c;
    e = 0;
    for (d = son; !nontrivial && d < eon; d = q + 1) {
      if (*d == REMOVED) { for (q = d + 1; *q; q++) ; continue; }
      lgl->stats.elm.steps++;
      lgl->stats.elm.resolutions++;
      LOGMCLS (3, c, "trying forced resolution 1st antecedent");
      LOGMCLS (3, d, "trying forced resolution 2nd antecedent");
      assert (clen > 0);
      reslen = clen - 1;
      for (q = d; (lit = *q); q++) {
	if (lit == -mpivot) continue;
        assert (lit != mpivot);
	idx = abs (lit), sgn = lglsgn (lit);
	tmp = lglpeek (&lgl->elm.mark, idx);
	if (tmp == -sgn) break;
	if (tmp != sgn) reslen++;
      }
      if (lit) {
	while (*++q) ;
        LOG (3, "trying forced resolution ends with trivial resolvent");
      } else {
	assert (!e);
	LOG (3, "non trivial resolvent in blocked clause elimination");
	nontrivial = INT_MAX;
      }
    }
    for (p = c; (lit = *p); p++) {
      if (lit == mpivot) continue;
      assert (lit != -mpivot);
      idx = abs (lit);
      assert (lglpeek (&lgl->elm.mark, idx) == lglsgn (lit));
      lglpoke (&lgl->elm.mark, idx, 0);
    }
    size = p - c;
    if (!nontrivial && (bintoo || size > 2)) {
      assert (maxcover >= cover);
      lgl->stats.elm.blkd++;
      LOGMCLS (2, c, "blocked on %d clause", ipivot);
      lglepush (lgl, 0);
      lglepush (lgl, ipivot);
      for (p = c; (lit = *p); p++) {
	if (lit == mpivot) continue;
	assert (lit != -mpivot);
	ilit = lglm2i (lgl, lit);
	lglepush (lgl, ilit);
      }
      lglelrmcls (lgl, ipivot, c, clidx);
      continue;
    }
    clidx++;
    if (lgl->limits.elm.steps <= lgl->stats.elm.steps) {
      LOG (2, "maximum number of steps in elmination exhausted");
      return;
    }
  }
}

static void lglelmfre (LGL * lgl, int bintoo) {
  int * sop, * eop, * son, * eon;
  assert (lgl->elm.pivot);
  sop = lgl->elm.lits.start + 1;
  eop = son = lgl->elm.lits.start + lgl->elm.neglidx;
  eon = lgl->elm.lits.top;
  lglelmfrelit (lgl, 1, sop, eop, son, eon, bintoo);
  lglelmfrelit (lgl, -1, son, eon, sop, eop, bintoo);
}

static int lglforcedvechk (LGL * lgl, int idx) {
  EVar * v = lglevar (lgl, idx);
  int pos = v->occ[0], neg = v->occ[1];
  int new, old;
  assert (0 <= pos && 0 <= neg);
  if (pos >= (1<<15)) return 0;
  if (neg >= (1<<15)) return 0;
  old = pos + neg;
  new = pos * neg;
  assert (0 <= old && 0 <= new);
  return new <= old + lgl->limits.elm.excess;
}

static void lgleliminated (LGL * lgl, int pivot) {
  AVar * av;
  int elit;
  Ext * e;
  av = lglavar (lgl, pivot);
  assert (av->type == FREEVAR);
  av->type = ELIMVAR;
  lgl->stats.elm.elmd++;
  assert (lgl->stats.elm.elmd > 0);
  lglflushlit (lgl, pivot);
  lglflushlit (lgl, -pivot);
  LOG (2, "eliminated %d", pivot);
  elit = lglexport (lgl, pivot);
  e = lglelit2ext (lgl, elit);
  assert (!e->eliminated);
  assert (!e->equiv);
  e->eliminated = 1;
}

static void lglepusheliminated (LGL * lgl, int idx) {
  const int * p, * w, * eow, * c, * l;
  int pivot, blit, tag, red, lit;
  EVar * ev = lglevar (lgl, idx);
  HTS * hts0;
  pivot = (ev->occ[0] <= ev->occ[1]) ? idx : -idx;
  hts0 = lglhts (lgl, pivot);
  w = lglhts2wchs (lgl, hts0);
  eow = w + hts0->count;
  LOG (3, "keeping clauses with %d for extending assignment", pivot);
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    red = blit & REDCS;
    if (red) continue;
    lglepush (lgl, 0);
    lglepush (lgl, pivot);
    if (tag == BINCS || tag == TRNCS) {
      lglepush (lgl, blit >> RMSHFT);
      if (tag == TRNCS)
	lglepush (lgl, *p);
    } else {
      assert (tag == IRRCS);
      c = lglidx2lits (lgl, 0, blit >> RMSHFT);
      for (l = c; (lit = *l); l++)
	if (lit != pivot)
	  lglepush (lgl, lit);
    }
  }
  lglepush (lgl, 0);
  lglepush (lgl, -pivot);
  lgleliminated (lgl, pivot);
}

static void lglforcedve (LGL * lgl, int idx) {
  const int * p0, * p1, * w0, * w1, * eow0, * eow1, * c0, * c1, * l0, * l1;
  int pivot, dummy0[4], dummy1[4], blit0, blit1, tag0, tag1, red0, red1;
  long deltairr, deltawchs;
  HTS * hts0, * hts1;
  int * wchs, * irr;
  int lit0, lit1;
  int unit = 0;
  EVar * ev;
  Val val;
  lglchkbcpclean (lgl);
  assert (!lgl->level);
  assert (lglforcedvechk (lgl, idx));
  if (lgl->elm.pivot) lglrstecls (lgl);
  LOG (2, "forced variable elimination of %d", idx);
  ev = lglevar (lgl, idx);
  pivot = (ev->occ[0] <= ev->occ[1]) ? idx : -idx;
  hts0 = lglhts (lgl, pivot);
  hts1 = lglhts (lgl, -pivot);
  w0 = lglhts2wchs (lgl, hts0);
  w1 = lglhts2wchs (lgl, hts1);
  eow0 = w0 + hts0->count;
  eow1 = w1 + hts1->count;
  dummy0[0] = pivot;
  dummy1[0] = -pivot;
  for (p0 = w0; !unit && p0 < eow0; p0++) {
    blit0 = *p0;
    tag0 = blit0 & MASKCS;
    if (tag0 == TRNCS || tag0 == LRGCS) p0++;
    red0 = blit0 & REDCS;
    if (red0) continue;
    if (tag0 == BINCS) {
      dummy0[1] = blit0 >> RMSHFT;
      dummy0[2] = 0;
      c0 = dummy0;
    } else if (tag0 == TRNCS) {
      dummy0[1] = blit0 >> RMSHFT;
      dummy0[2] = *p0;
      dummy0[3] = 0;
      c0 = dummy0;
    } else {
      assert (tag0 == IRRCS);
      c0 = lglidx2lits (lgl, 0, blit0 >> RMSHFT);
    }
    for (l0 = c0; (lit0 = *l0); l0++) {
      assert (!lglmarked (lgl, lit0));
      lglmark (lgl, lit0);
    }
    for (p1 = w1; !unit && p1 < eow1; p1++) {
      blit1 = *p1;
      tag1 = blit1 & MASKCS;
      if (tag1 == TRNCS || tag1 == LRGCS) p1++;
      red1 = blit1 & REDCS;
      if (red1) continue;
      if (tag1 == BINCS) {
	dummy1[1] = blit1 >> RMSHFT;
	dummy1[2] = 0;
	c1 = dummy1;
      } else if (tag1 == TRNCS) {
	dummy1[1] = blit1 >> RMSHFT;
	dummy1[2] = *p1;
	dummy1[3] = 0;
	c1 = dummy1;
      } else {
	assert (tag1 == IRRCS);
	c1 = lglidx2lits (lgl, 0, blit1 >> RMSHFT);
      }
      lgl->stats.elm.steps++;
      lgl->stats.elm.resolutions++;
      for (l1 = c1; (lit1 = *l1); l1++)
	if (lit1 != -pivot && lglmarked (lgl, lit1) < 0) break;
      if (lit1) continue;
      LOGCLS (3, c0, "resolving forced variable elimination 1st antecedent");
      LOGCLS (3, c1, "resolving forced variable elimination 2nd antecedent");
      assert (lglmtstk (&lgl->clause));
      for (l0 = c0; (lit0 = *l0); l0++) {
	if (lit0 == pivot) continue;
	val = lglval (lgl, lit0);
	assert (val <= 0);
	if (val < 0) continue;
	lglpushstk (lgl, &lgl->clause, lit0);
      }
      for (l1 = c1; (lit1 = *l1); l1++) {
	if (lit1 == -pivot) continue;
	val = lglval (lgl, lit1);
	assert (val <= 0);
	if (val < 0) continue;
	if (lglmarked (lgl, lit1)) continue;
	lglpushstk (lgl, &lgl->clause, lit1);
      }
      lglpushstk (lgl, &lgl->clause, 0);
      LOGCLS (3, lgl->clause.start, "forced variable elimination resolvent");
      if (lglcntstk (&lgl->clause) >= 3) {
	wchs = lgl->wchs.start;
	irr = lgl->irr.start;
	lgladdcls (lgl, 0, 0);
	deltawchs = lgl->wchs.start - wchs;
	if (deltawchs) {
	  p0 += deltawchs, w0 += deltawchs, eow0 += deltawchs;
	  p1 += deltawchs, w1 += deltawchs, eow1 += deltawchs;
	}
	deltairr = lgl->irr.start - irr;
	if (deltairr && tag0 == IRRCS) c0 += deltairr;
	lglclnstk (&lgl->clause);
      } else {
	assert (lglcntstk (&lgl->clause) == 2);
	lglunit (lgl, lgl->clause.start[0]);
	lglclnstk (&lgl->clause);
	unit = 1;
      }
    }
    for (l0 = c0; (lit0 = *l0); l0++) {
      assert (lglmarked (lgl, lit0));
      lglunmark (lgl, lit0);
    }
  }
  if (unit) return;
  lglepusheliminated (lgl, pivot);
  lgl->stats.elm.forced++;
}

static int lglunhimpl (const DFPR * dfpr, int a, int b) {
  int u = lglulit (a), v = lglulit (b), c, d, f, g;
  c = dfpr[u].discovered; if (!c) return 0;
  d = dfpr[v].discovered; if (!d) return 0;
  f = dfpr[u].finished, g = dfpr[v].finished;
  assert (0 < c && c < f);
  assert (0 < d && d < g);
  return c < d && g < f;
}

static int lglunhimplies2 (const DFPR * dfpr, int a, int b) {
  return lglunhimpl (dfpr, a, b) || lglunhimpl (dfpr, -b, -a);
}

static int lglunhimplincl (const DFPR * dfpr, int a, int b) {
  int u = lglulit (a), v = lglulit (b), c, d, f, g;
  c = dfpr[u].discovered; if (!c) return 0;
  d = dfpr[v].discovered; if (!d) return 0;
  f = dfpr[u].finished, g = dfpr[v].finished;
  assert (0 < c && c < f);
  assert (0 < d && d < g);
  return c <= d && g <= f;
}

static int lglunhimplies2incl (const DFPR * dfpr, int a, int b) {
  return lglunhimplincl (dfpr, a, b) || lglunhimplincl (dfpr, -b, -a);
}

#define ENLDF(POSNEG) \
do { \
  int OLDSIZE = lgl->df.POSNEG.szdfs; \
  int NEWSIZE = OLDSIZE ? 2*OLDSIZE : 1; \
  RSZ (lgl->df.POSNEG.dfs, OLDSIZE, NEWSIZE); \
  lgl->df.POSNEG.szdfs = NEWSIZE; \
} while (0)

#define PUSHDF(POSNEG,LIT) \
do { \
  unsigned ULIT = lglulit (LIT); \
  int discovered = dfpr[ULIT].discovered; \
  DF * DF; \
  if (!discovered) break; \
  if (lgl->df.POSNEG.ndfs == lgl->df.POSNEG.szdfs) ENLDF (POSNEG); \
  DF = lgl->df.POSNEG.dfs + lgl->df.POSNEG.ndfs++; \
  DF->discovered = discovered; \
  DF->finished = dfpr[ULIT].finished; \
} while (0)

static int lglcmpdf (const DF * a, const DF * b) {
  return a->discovered - b->discovered;
}

static int lgluhte (LGL * lgl, const DFPR * dfpr, Stk * s) {
  int size = lglcntstk (s), i, p, n, lit;
  if (size <= 2 || size > lgl->opts.elmhtelim.val) return 0;
  lgl->df.pos.ndfs = lgl->df.neg.ndfs = 0;
  for (i = 0; i < size; i++) {
    lit = s->start[i];
    PUSHDF (pos, lit);
    PUSHDF (neg, -lit);
  }
  if (!lgl->df.pos.ndfs || !lgl->df.neg.ndfs) return 0;
  SORT (lgl->df.pos.dfs, lgl->df.pos.ndfs, lglcmpdf);
  SORT (lgl->df.neg.dfs, lgl->df.neg.ndfs, lglcmpdf);
  p = n = 0;
  for (;;) {
    if (lgl->df.neg.dfs[n].discovered > lgl->df.pos.dfs[p].discovered) {
      if (++p == lgl->df.pos.ndfs) return 0;
    } else if (lgl->df.neg.dfs[n].finished < lgl->df.pos.dfs[p].finished) {
      if (++n == lgl->df.neg.ndfs) return 0;
    } else return 1;
  }
}

static int lgltryforcedve (LGL * lgl, int idx) {
  if (lgl->limits.elm.steps <= lgl->stats.elm.steps) return 1;
  if (!lglforcedvechk (lgl, idx)) return 0;
  lglforcedve (lgl, idx);
  return 1;
}

static int lgltrylargeve (LGL * lgl, DFPR * dfpr) {
  const int * c, * d, * sop, * eop, * son, * eon, * p, * q, * start, * end;
  int lit, idx, sgn, tmp, ip, mp, ilit, npocc, nnocc, limit, count, occ, i;
  int clen, dlen, reslen, maxreslen;
  EVar * ev;
  Val val;
  ip = lgl->elm.pivot;
  assert (ip);
  sop = lgl->elm.lits.start + 1;
  eop = son = lgl->elm.lits.start + lgl->elm.neglidx;
  eon = lgl->elm.lits.top;
  npocc = lglpeek (&lgl->elm.noccs, lglulit (1));
  nnocc = lglpeek (&lgl->elm.noccs, lglulit (-1));
  limit = npocc + nnocc;
  count = 0;
  for (i = 0; i <= 1; i++) {
    start = i ? son : sop;
    end = i ? eon : eop;
    for (c = start; c < end; c++) {
      if (*c == REMOVED) { while (*c) c++; continue; }
      while ((lit = *c)) {
	ilit = lglm2i (lgl, lit);
	ev = lglevar (lgl, ilit);
	sgn = lglsgn (ilit);
	occ = ev->occ[sgn];
	if (occ > lgl->opts.elmocclim.val) {
	  LOG (3, "number of occurrences of %d larger than limit", ilit);
	  return 0;
	}
	c++;
      }
      count++;
    }
  }
  assert (count == limit);
  limit += lgl->limits.elm.excess;
  LOG (3, "trying clause distribution for %d with limit %d", ip, limit);
  maxreslen = 0;
  for (c = sop; c < eop && limit >= 0; c = p + 1) {
    if (*c == REMOVED) { for (p = c + 1; *p; p++) ; continue; }
    assert (lglmtstk (&lgl->resolvent));
    clen = 0;
    for (p = c; (lit = *p); p++) {
      if (lit == 1) continue;
      assert (lit != -1);
      idx = abs (lit);
      assert (!lglpeek (&lgl->elm.mark, idx));
      sgn = lglsgn (lit);
      lglpoke (&lgl->elm.mark, idx, sgn);
      ilit = lglm2i (lgl, lit);
      lglpushstk (lgl, &lgl->resolvent, ilit);
      clen++;
    }
    for (d = son; limit >= 0 && d < eon; d = q + 1) {
      if (*d == REMOVED) { for (q = d + 1; *q; q++) ; continue; }
      lgl->stats.elm.steps++;
      lgl->stats.elm.resolutions++;
      LOGMCLS (3, c, "trying resolution 1st antecedent");
      LOGMCLS (3, d, "trying resolution 2nd antecedent");
      dlen = 0;
      reslen = clen;
      for (q = d; (lit = *q); q++) {
	if (lit == -1) continue;
	dlen++;
	assert (lit != 1);
	idx = abs (lit), sgn = lglsgn (lit);
	tmp = lglpeek (&lgl->elm.mark, idx);
	if (tmp == -sgn) break;
	if (tmp == sgn) continue;
	ilit = lglm2i (lgl, lit);
	lglpushstk (lgl, &lgl->resolvent, ilit);
	reslen++;
      }
      assert (reslen == lglcntstk (&lgl->resolvent));
      if (!lit && reslen == 1) {
        LOG (3, "trying resolution ends with unit clause");
	lit = lglpeek (&lgl->resolvent, 0);
	limit += lglevar (lgl, lit)->occ[lit < 0];
      } else if (lit) {
	while (*++q) ;
        LOG (3, "trying resolution ends with trivial resolvent");
      } else if (dfpr && 
                 (reslen > 2 || clen > 1 || dlen > 1) &&
                 lgluhte (lgl, dfpr, &lgl->resolvent)) {
        LOG (3, "trying resolution ends with hidden tautology");
      } else {
        limit--;
        LOG (3,
	     "trying resolution with non trivial resolvent remaining %d",
	     limit);
	if (reslen > maxreslen) maxreslen = reslen;
      }
      assert (!*q);
      lglrststk (&lgl->resolvent, clen);
    }
    lglclnstk (&lgl->resolvent);
    for (p = c; (lit = *p); p++) {
      if (lit == 1) continue;
      assert (lit != -1);
      idx = abs (lit);
      assert (lglpeek (&lgl->elm.mark, idx) == lglsgn (lit));
      lglpoke (&lgl->elm.mark, idx, 0);
    }
    if (lgl->limits.elm.steps <= lgl->stats.elm.steps) {
      LOG (2, "maximum number of steps in elmination exhausted");
      return 0;
    }
    if (maxreslen > lgl->opts.elmreslim.val) {
      LOG (3, "maximum resolvent size in elimination reached");
      return 0;
    }
  }
  assert (lglm2i (lgl, 1) == ip);
  if (limit < 0) {
    LOG (3, "resolving away %d would increase number of clauses", ip);
    return 0;
  }
  if (limit) LOG (2, "resolving away %d removes %d clauses", ip, limit);
  else LOG (2, "resolving away %d does not change number of clauses", ip);
  LOG (2, "variable elimination of %d", lgl->elm.pivot);
  lglflushlit (lgl, ip);
  lglflushlit (lgl, -ip);
  if (npocc < nnocc) start = sop, end = eop, mp = 1;
  else start = son, end = eon, ip = -ip, mp = -1;
  LOG (3, "will save clauses with %d for extending assignment", ip);
  for (c = start; c < end; c = p + 1) {
    if (*c == REMOVED) { for (p = c + 1; *p; p++) ; continue; }
    lglepush (lgl, 0);
    lglepush (lgl, ip);
    for (p = c; (lit = *p); p++)  {
      if (lit == mp) continue;
      assert (lit != -mp);
      ilit = lglm2i (lgl, lit);
      lglepush (lgl, ilit);
    }
  }
  lglepush (lgl, 0);
  lglepush (lgl, -ip);
  for (c = sop; c < eop; c = p + 1) {
    if (*c == REMOVED) { for (p = c + 1; *p; p++) ; continue; }
    assert (lglmtstk (&lgl->resolvent));
    clen = 0;
    for (p = c; (lit = *p); p++) {
      if (lit == 1) continue;
      assert (lit != -1);
      idx = abs (lit);
      assert (!lglpeek (&lgl->elm.mark, idx));
      sgn = lglsgn (lit);
      lglpoke (&lgl->elm.mark, idx, sgn);
      ilit = lglm2i (lgl, lit);
      lglpushstk (lgl, &lgl->resolvent, ilit);
      clen++;
    }
    for (d = son; limit >= 0 && d < eon; d = q + 1) {
      if (*d == REMOVED) { for (q = d + 1; *q; q++) ; continue; }
      lgl->stats.elm.steps++;
      lgl->stats.elm.resolutions++;
      assert (lglmtstk (&lgl->clause));
      dlen = 0;
      reslen = clen;
      for (q = d; (lit = *q); q++) {
	if (lit == -1) continue;
	dlen++;
	assert (lit != 1);
	idx = abs (lit), sgn = lglsgn (lit);
	tmp = lglpeek (&lgl->elm.mark, idx);
	if (tmp == sgn) continue;
	if (tmp == -sgn) break;
	ilit = lglm2i (lgl, lit);
	val = lglval (lgl, ilit);
	if (val < 0) continue;
	if (val > 0) break;
	lglpushstk (lgl, &lgl->clause, ilit);
	ilit = lglm2i (lgl, lit);
	lglpushstk (lgl, &lgl->resolvent, ilit);
	reslen++;
      }
      assert (reslen == lglcntstk (&lgl->resolvent));
      if (!lit && reslen == 1) {
	goto RESOLVE;
      } if (lit) {
	while (*++q) ;
      } else if (dfpr && 
                 (reslen > 2 || clen > 1 || dlen > 1) &&
                 lgluhte (lgl, dfpr, &lgl->resolvent)) {
	lgl->stats.elm.htes++;
      } else {
RESOLVE:
	LOGMCLS (3, c, "resolving variable elimination 1st antecedent");
	LOGMCLS (3, d, "resolving variable elimination 2nd antecedent");
	for (p = c; (lit = *p); p++) {
	  if (lit == 1) continue;
	  assert (lit != -1);
	  ilit = lglm2i (lgl, lit);
	  val = lglval (lgl, ilit);
	  if (val < 0) continue;
	  if (val > 0) break;
	  lglpushstk (lgl, &lgl->clause, ilit);
	}
	if (!lit) {
	  lglpushstk (lgl, &lgl->clause, 0);
	  LOGCLS (3, lgl->clause.start, "variable elimination resolvent");
	  lgladdcls (lgl, 0, 0);
	}
      }
      lglclnstk (&lgl->clause);
      assert (!*q);
      lglrststk (&lgl->resolvent, clen);
    }
    lglclnstk (&lgl->resolvent);
    for (p = c; (lit = *p); p++) {
      if (lit == 1) continue;
      assert (lit != -1);
      idx = abs (lit);
      assert (lglpeek (&lgl->elm.mark, idx) == lglsgn (lit));
      lglpoke (&lgl->elm.mark, idx, 0);
    }
  }
  lgleliminated (lgl, lgl->elm.pivot);
  lgl->stats.elm.large++;
  return 1;
}

static void lglelimlitaux (LGL * lgl, DFPR * dfpr, int idx) {
  lglelmsub (lgl);
  if (lglstr (lgl) && lglelmstr (lgl)) return;
  if (lgltryforcedve (lgl, idx)) return;
  lglelmfre (lgl, !dfpr);
  if (lgltryforcedve (lgl, idx)) return;
  lgltrylargeve (lgl, dfpr);
}

static int lgls2m (LGL * lgl, int ilit) {
  AVar * av = lglavar (lgl, ilit);
  int res = av->mark;
  if (!res) {
    res = lglcntstk (&lgl->seen) + 1;
    if (res > lgl->opts.smallvevars.val + 1) return 0;
    av->mark = res;
    assert (lglcntstk (&lgl->seen) == lglcntstk (&lgl->elm.m2i) - 1);
    lglpushstk (lgl, &lgl->seen, abs (ilit));
    lglpushstk (lgl, &lgl->elm.m2i, abs (ilit));
    LOG (4, "mapped internal variable %d to marked variable %d",
         abs (ilit), res);
  }
  if (ilit < 0) res = -res;
  return res;
}

static void lglvar2funaux (int v, Fun res, int negate) {
  uint64_t tmp;
  int i, j, p;
  assert (0 <= v && v < FUNVAR);
  if (v < 6) {
    tmp = lglbasevar2funtab[v];
    if (negate) tmp = ~tmp;
    for (i = 0; i < FUNQUADS; i++)
      res[i] = tmp;
  } else {
    tmp = negate ? ~0ull : 0ull;
    p = 1 << (v - 6);
    j = 0;
    for (i = 0; i < FUNQUADS; i++) {
      res[i] = tmp;
      if (++j < p) continue;
      tmp = ~tmp;
      j = 0;
    }
  }
}

static void lglvar2fun (int v, Fun res) {
  lglvar2funaux (v, res, 0);
}

static void lglnegvar2fun (int v, Fun res) {
  lglvar2funaux (v, res, 1);
}

static void lglfuncpy (Fun dst, const Fun src) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    dst[i] = src[i];
}

static void lglfalsefun (Fun res) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    res[i] = 0ll;
}

static void lgltruefun (Fun res) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    res[i] = ~0ll;
}

static int lglisfalsefun (const Fun f) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    if (f[i] != 0ll) return 0;
  return 1;
}

static int lglistruefun (const Fun f) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    if (f[i] != ~0ll) return 0;
  return 1;
}

static void lglorfun (Fun a, const Fun b) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    a[i] |= b[i];
}

static void lglornegfun (Fun a, const Fun b) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    a[i] |= ~b[i];
}

static void lglor3fun (Fun a, const Fun b, const Fun c) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    a[i] = b[i] | c[i];
}

static void lglor3negfun (Fun a, const Fun b, const Fun c) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    a[i] = b[i] | ~c[i];
}

static void lglandornegfun (Fun a, const Fun b, const Fun c) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    a[i] &= b[i] | ~c[i];
}

static void lglandfun (Fun a, const Fun b) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    a[i] &= b[i];
}

static void lgland3fun (Fun a, const Fun b, const Fun c) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    a[i] = b[i] & c[i];
}

static void lgland3negfun (Fun a, const Fun b, const Fun c) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    a[i] = b[i] & ~c[i];
}

static void lglsrfun (Fun a, int shift) {
  uint64_t rest, tmp;
  int i, j, q, b, l;
  assert (0 <= shift);
  b = shift & 63;
  q = shift >> 6;
  j = 0;
  i = j + q;
  assert (i >= 0);
  l = 64 - b;
  while (j < FUNQUADS) {
    if (i < FUNQUADS) {
      tmp = a[i] >> b;
      rest = (b && i+1 < FUNQUADS) ? (a[i+1] << l) : 0ull;
      a[j] = rest | tmp;
    } else a[j] = 0ull;
    i++, j++;
  }
}

static void lglslfun (Fun a, int shift) {
  uint64_t rest, tmp;
  int i, j, q, b, l;
  assert (0 <= shift);
  b = shift & 63;
  q = shift >> 6;
  j = FUNQUADS - 1;
  i = j - q;
  l = 64 - b;
  while (j >= 0) {
    if (i >= 0) {
      tmp = a[i] << b;
      rest = (b && i > 0) ? (a[i-1] >> l) : 0ll;
      a[j] = rest | tmp;
    } else a[j] = 0ll;
    i--, j--;
  }
}

static void lgls2fun (int mlit, Fun res) {
  int midx = abs (mlit), sidx = midx - 2;
  assert (0 <= sidx && sidx < FUNVAR);
  if (mlit < 0) lglnegvar2fun (sidx, res);
  else lglvar2fun (sidx, res);
}

static int lglinitsmallve (LGL * lgl, int lit, Fun res) {
  int blit, tag, red, other, other2, lidx, mlit;
  const int * p, * w, * eow, * c, * q;
  Fun cls, tmp;
  HTS * hts;
  Val val;
  assert (!lglval (lgl, lit));
  LOG (3, "initializing small variable eliminiation for %d", lit);
  mlit = lgls2m (lgl, lit);
  assert (abs (mlit) == 1);
  hts = lglhts (lgl, lit);
  lgltruefun (res);
  if (!hts->count) goto DONE;
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    red = blit & REDCS;
    if (red) continue;
    lglfalsefun (cls);
    if (tag == BINCS || tag == TRNCS) {
      other = blit >> RMSHFT;
      val = lglval (lgl, other);
      assert (val <= 0);
      if (!val) {
	mlit = lgls2m (lgl, other);
	if (!mlit) return 0;
	lgls2fun (mlit, tmp);
	lglorfun (cls, tmp);
      }
      if (tag == TRNCS) {
        other2 = *p;
	val = lglval (lgl, other2);
	assert (val <= 0);
	if (!val) {
	  mlit = lgls2m (lgl, other2);
	  if (!mlit) return 0;
	  lgls2fun (mlit, tmp);
	  lglorfun (cls, tmp);
	}
      }
    } else {
      assert (tag == IRRCS);
      lidx = blit >> RMSHFT;
      c = lglidx2lits (lgl, 0, lidx);
      for (q = c; (other = *q); q++) {
	if (other == lit) continue;
	assert (other != -lit);
	val = lglval (lgl, other);
	assert (val <= 0);
	if (!val) {
	  mlit = lgls2m (lgl, other);
	  if (!mlit) return 0;
	  lgls2fun (mlit, tmp);
	  lglorfun (cls, tmp);
	}
      }
    }
    assert (!lglisfalsefun (cls));
    assert (!lglistruefun (cls));
    lglandfun (res, cls);
    lgl->stats.elm.steps++;
    lgl->stats.elm.copies++;
  }
DONE:
  return 1;
}

static void lglresetsmallve (LGL * lgl) {
  lglclnstk (&lgl->elm.m2i);
  lglclnstk (&lgl->clv);
  lglpopnunmarkstk (lgl, &lgl->seen);
}

static void lglsmallevalcls (unsigned cls, Fun res) {
  Fun tmp;
  int v;
  lglfalsefun (res);
  for (v = 0; v < FUNVAR; v++) {
    if (cls & (1 << (2*v + 1))) {
      lglvar2fun (v, tmp);
      lglornegfun (res, tmp);
    } else if (cls & (1 << (2*v))) {
      lglvar2fun (v, tmp);
      lglorfun (res, tmp);
    }
  }
}

static Cnf lglpos2cnf (int pos) { assert (pos >=0 ); return pos; }
static Cnf lglsize2cnf (int s) { assert (s >=0 ); return ((Cnf)s) << 32; }
static int lglcnf2pos (Cnf cnf) { return cnf & 0xfffffll; }
static int lglcnf2size (Cnf cnf) { return cnf >> 32; }

static Cnf lglcnf (int pos, int size) {
  return lglpos2cnf (pos) | lglsize2cnf (size);
}

static void lglsmallevalcnf (LGL * lgl, Cnf cnf, Fun res) {
  Fun tmp;
  int i, n, p, cls;
  p = lglcnf2pos (cnf);
  n = lglcnf2size (cnf);
  lgltruefun (res);
  for (i = 0; i < n; i++) {
    cls = lglpeek (&lgl->clv, p + i);
    lglsmallevalcls (cls, tmp);
    lglandfun (res, tmp);
  }
}

static void lglnegcofactorfun (const Fun f, int v, Fun res) {
  Fun mask, masked;
  lglvar2fun (v, mask);
  lgland3negfun (masked, f, mask);
  lglfuncpy (res, masked);
  lglslfun (masked, (1 << v));
  lglorfun (res, masked);
}

static void lglposcofactorfun (const Fun f, int v, Fun res) {
  Fun mask, masked;
  lglvar2fun (v, mask);
  lgland3fun (masked, f, mask);
  lglfuncpy (res, masked);
  lglsrfun (masked, (1 << v));
  lglorfun (res, masked);
}

static int lgleqfun (const Fun a, const Fun b) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    if (a[i] != b[i]) return 0;
  return 1;
}

static int lglsmalltopvar (const Fun f, int min) {
  Fun p, n;
  int v;
  for (v = min; v < FUNVAR; v++) {
    lglposcofactorfun (f, v, p);
    lglnegcofactorfun (f, v, n);
    if (!lgleqfun (p, n)) return v;
  }
  return v;
}

static Cnf lglsmalladdlit2cnf (LGL * lgl, Cnf cnf, int lit) {
  int p, m, q, n, i, cls;
  Cnf res;
  p = lglcnf2pos (cnf);
  m = lglcnf2size (cnf);
  q = lglcntstk (&lgl->clv);
  for (i = 0; i < m; i++) {
    cls = lglpeek (&lgl->clv, p + i);
    assert (!(cls & lit));
    cls |= lit;
    lglpushstk (lgl, &lgl->clv, cls);
  }
  n = lglcntstk (&lgl->clv) - q;
  res = lglcnf (q, n);
  return res;
}

#ifndef NDEBUG
static int lglefun (const Fun a, const Fun b) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    if (a[i] & ~b[i]) return 0;
  return 1;
}
#endif

static Cnf lglsmallipos (LGL * lgl, const Fun U, const Fun L, int min) {
  Fun U0, U1, L0, L1, Unew, ftmp;
  Cnf c0, c1, cstar, ctmp, res;
  int x, y, z;
  assert (lglefun (L, U));
  if (lglistruefun (U)) return TRUECNF;
  if (lglisfalsefun (L)) return FALSECNF;
  assert (min < lglcntstk (&lgl->elm.m2i));
  y = lglsmalltopvar (U, min);
  z = lglsmalltopvar (L, min);
  x = (y < z) ? y : z;
  assert (x < FUNVAR);
  lglnegcofactorfun (U, x, U0); lglposcofactorfun (U, x, U1);
  lglnegcofactorfun (L, x, L0); lglposcofactorfun (L, x, L1);
  lglor3negfun (ftmp, U0, L1);
  c0 = lglsmallipos (lgl, ftmp, L0, min+1);
  lglor3negfun (ftmp, U1, L0);
  c1 = lglsmallipos (lgl, ftmp, L1, min+1);
  lglsmallevalcnf (lgl, c0, ftmp);
  lglor3negfun (Unew, U0, ftmp);
  lglsmallevalcnf (lgl, c1, ftmp);
  lglandornegfun (Unew, U1, ftmp);
  lglor3fun (ftmp, L0, L1);
  cstar = lglsmallipos (lgl, Unew, ftmp, min+1);
  assert (cstar != FALSECNF);
  ctmp = lglsmalladdlit2cnf (lgl, c1, (1 << (2*x + 1)));
  res = lglcnf2pos (ctmp);
  ctmp = lglsmalladdlit2cnf (lgl, c0, (1 << (2*x)));
  if (res == TRUECNF) res = lglcnf2pos (ctmp);
  ctmp = lglsmalladdlit2cnf (lgl, cstar, 0);
  if (res == TRUECNF) res = lglcnf2pos (ctmp);
  res |= lglsize2cnf (lglcntstk (&lgl->clv) - res);
  return res;
}

static void lglsmallve (LGL * lgl, Cnf cnf) {
  int * soc = lgl->clv.start + lglcnf2pos (cnf);
  int * eoc = soc + lglcnf2size (cnf);
  int * p, cls, v, lit, trivial;
  Val val;
  for (p = soc; !lgl->mt && p < eoc; p++) {
    cls = *p;
    assert (lglmtstk (&lgl->clause));
    trivial = 0;
    for (v = 0; v < FUNVAR; v++) {
      if (cls & (1 << (2*v + 1))) lit = -lglm2i (lgl, v+2);
      else if (cls & (1 << (2*v))) lit = lglm2i (lgl, v+2);
      else continue;
      val = lglval (lgl, lit);
      if (val < 0) continue;
      if (val > 0) trivial = 1;
      lglpushstk (lgl, &lgl->clause, lit);
    }
    if (!trivial) {
      lgl->stats.elm.steps++;
      lgl->stats.elm.resolutions++;
      lglpushstk (lgl, &lgl->clause, 0);
      LOGCLS (3, lgl->clause.start, "small elimination resolvent");
#ifndef NLGLPICOSAT
      lglpicosatchkcls (lgl);
#endif
      lgladdcls (lgl, 0, 0);
    }
    lglclnstk (&lgl->clause);
  }
}

static int lglsmallisunitcls (LGL * lgl, int cls) {
  int fidx, fsign, flit, mlit, ilit;
  ilit = 0;
  for (fidx = 0; fidx < FUNVAR; fidx++)
    for (fsign = 0; fsign <= 1; fsign++) {
      flit = 1<<(2*fidx + fsign);
      if (!(cls & flit)) continue;
      if (ilit) return 0;
      mlit = (fidx + 2) * (fsign ? -1 : 1);
      ilit = lglm2i (lgl, mlit);
    }
  return ilit;
}

static int lglsmallcnfunits (LGL * lgl, Cnf cnf) {
  int p, m, i, res, cls, ilit;
  p = lglcnf2pos (cnf);
  m = lglcnf2size (cnf);
  res = 0;
  for (i = 0; i < m; i++) {
    cls = lglpeek (&lgl->clv, p + i);
    ilit = lglsmallisunitcls (lgl, cls);
    if (!ilit) continue;
    assert (lglval (lgl, ilit) >= 0);
    lglunit (lgl, ilit);
    res++;
  }
  return res;
}

static int lgltrysmallve (LGL * lgl, int idx) {
  int res = 0, new, old, units;
  Fun pos, neg, fun;
  EVar * ev;
  Cnf cnf;
  assert (lglmtstk (&lgl->elm.m2i));
  assert (lglmtstk (&lgl->seen));
  assert (lglmtstk (&lgl->clv));
  lglpushstk (lgl, &lgl->elm.m2i, 0);
  lglpushstk (lgl, &lgl->clv, 0);
  if (lglinitsmallve (lgl, idx, pos) && lglinitsmallve (lgl, -idx, neg)) {
    lglor3fun (fun, pos, neg);
    cnf = lglsmallipos (lgl, fun, fun, 0);
    new = lglcnf2size (cnf);
    units = lglsmallcnfunits (lgl, cnf);
    assert (units <= new);
    new -= units;
    ev = lglevar (lgl, idx);
    old = ev->occ[0] + ev->occ[1];
    LOG (2, "small elimination of %d replaces "
            "%d old with %d new clauses and %d units",
         idx, old, new, units);
    lgl->stats.elm.small.tried++;
    if (new <= old + lgl->limits.elm.excess) {
      LOG (2, "small elimination of %d removes %d clauses", idx, old - new);
      lglsmallve (lgl, cnf);
      lglepusheliminated (lgl, idx);
      lgl->stats.elm.small.elm++;
      res = 1;
    } else {
      LOG (2, "small elimination of %d would add %d clauses", idx, new - old);
      if (units > 0) res = 1;
      else lgl->stats.elm.small.failed++;
    }
  } else LOG (2, "too many variables for small elimination");
  lglresetsmallve (lgl);
  return res;
}

static void lglelimlit (LGL * lgl, DFPR * dfpr, int idx) {
  if (!lglisfree (lgl, idx)) return;
  if (!lglchkoccs4elm (lgl, idx)) return;
  LOG (2, "trying to eliminate %d", idx);
  if (!dfpr &&
      lglstr (lgl) &&
      lgl->opts.smallve.val &&
      lgltrysmallve (lgl, idx)) return;
  if (lgltryforcedve (lgl, idx)) return;
  lglinitecls (lgl, idx);
  lglelimlitaux (lgl, dfpr, idx);
  if (lgl->elm.pivot) lglrstecls (lgl);
}

static int lglblockcls (LGL * lgl, int lit) {
  int blit, tag, red, other, other2, lidx, val, count, size;
  const int * p, * w, * eow, * c, *l;
  HTS * hts;
  hts = lglhts (lgl, lit);
  hts = lglhts (lgl, lit);
  if (!hts->count) return 1;
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  count = 0;
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    red = blit & REDCS;
    if (red) continue;
    count++;
    lgl->stats.blk.res++;
    if (tag == BINCS || tag == TRNCS) {
      other = blit >> RMSHFT;
      val = lglmarked (lgl, other);
      if (val < 0) continue;
      if (tag == TRNCS) {
	other2 = *p;
	val = lglmarked (lgl, other2);
	if (val < 0) continue;
      }
    } else {
      assert (tag == IRRCS);
      lidx = blit >> RMSHFT;
      c = lglidx2lits (lgl, 0, lidx);
      size = 0;
      for (l = c; (other = *l); l++) {
	val = lglmarked (lgl, other);
	if (++size > lgl->opts.blkclslim.val) return 0;
	if (val < 0) break;
      }
      if (other) continue;
    }
    return 0;
  }
  LOG (3, "resolved %d trivial resolvents on %d", count, lit);
  return 1;
}

static void lglpushnmarkseen (LGL * lgl, int lit) {
  assert (!lglmarked (lgl, lit));
  lglpushstk (lgl, &lgl->seen, lit);
  lglmark (lgl, lit);
}

static int lgl2manyoccs4blk (LGL * lgl, int lit) {
  return lglhts (lgl, lit)->count > lgl->opts.blkocclim.val;
}

static void lglblocking (LGL * lgl, int ilit) {
  int elit = lglexport (lgl, ilit), sgnbit = (1 << (elit < 0));
  Ext * ext = lglelit2ext (lgl, elit);
  assert (!ext->equiv);
  assert (!ext->eliminated);
  assert (abs (ext->repr) == abs (ilit));
  if (ext->blocking & sgnbit) return;
  ext->blocking |= sgnbit;
  LOG (3, "marking external %d internal %d as blocking", elit, ilit);
  lgl->stats.blk.lits++;
}

static int lglblocklit (LGL * lgl, int lit, Stk * stk) {
  int blit, tag, red, blocked, other, other2, lidx, count, size;
  int * p, * w, * eow, * c, * l;
  HTS * hts;
  if (lglval (lgl, lit)) return 0;
  hts = lglhts (lgl, lit);
  if (!hts->count) return 0;
  if (lgl2manyoccs4blk (lgl, lit)) return 0;
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  count = 0;
  assert (lglmtstk (stk+2) && lglmtstk (stk+3) && lglmtstk (stk+4));
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    blocked = 0;
    if (tag == TRNCS || tag == LRGCS) p++;
    red = blit & REDCS;
    if (red) continue;
    assert (lglmtstk (&lgl->seen));
    if (tag == BINCS || tag == TRNCS) {
      other = blit >> RMSHFT;
      if (lgl2manyoccs4blk (lgl, other)) continue;
      lglpushnmarkseen (lgl, other);
      if (tag == TRNCS) {
	other2 = *p;
        if (lgl2manyoccs4blk (lgl, other2)) goto CONTINUE;
	lglpushnmarkseen (lgl, other2);
      }
    } else {
      assert (tag == IRRCS);
      lidx = blit >> RMSHFT;
      c = lglidx2lits (lgl, 0, lidx);
      size = 0;
      for (l = c; (other = *l); l++) {
	if (other == lit) continue;
        if (lgl2manyoccs4blk (lgl, other)) goto CONTINUE;
	if (++size > lgl->opts.blkclslim.val) goto CONTINUE;
	lglpushnmarkseen (lgl, other);
      }
    }
    blocked = lglblockcls (lgl, -lit);
CONTINUE:
    lglpopnunmarkstk (lgl, &lgl->seen);
    if (!blocked) continue;
    if (tag == BINCS) {
      other = blit >> RMSHFT;
      lglpushstk (lgl, stk+2, other);
    } else if (tag == TRNCS) {
      other = blit >> RMSHFT;
      lglpushstk (lgl, stk+3, other);
      other2 = *p;
      lglpushstk (lgl, stk+3, other2);
    } else {
      assert (tag == IRRCS);
      lidx = blit >> RMSHFT;
      lglpushstk (lgl, stk+4, lidx);
    }
  }
  while (!lglmtstk (stk+2)) {
    count++;
    other = lglpopstk (stk+2);
    LOG (2, "blocked binary clause %d %d on %d", lit, other, lit);
    lglrmbcls (lgl, lit, other, 0);
    lglepush (lgl, 0);
    lglepush (lgl, lit);
    lglepush (lgl, other);
  }
  while (!lglmtstk (stk+3)) {
    count++;
    other2 = lglpopstk (stk+3);
    other = lglpopstk (stk+3);
    LOG (2, "blocked ternary clause %d %d %d on %d", lit, other, other2, lit);
    lglrmtcls (lgl, lit, other, other2, 0);
    lglepush (lgl, 0);
    lglepush (lgl, lit);
    lglepush (lgl, other);
    lglepush (lgl, other2);
  }
  while (!lglmtstk (stk+4)) {
    lidx = lglpopstk (stk+4);
    count++;
    c = lglidx2lits (lgl, 0, lidx);
    LOGCLS (2, c, "blocked on %d large clause", lit);
    lglepush (lgl, 0);
    lglepush (lgl, lit);
    for (l = c; (other = *l); l++)
      if (other != lit) lglepush (lgl, other);
    lglrmlcls (lgl, lidx, 0);
  }
  LOG (2, "found %d blocked clauses with %d", count, lit);
  lgl->stats.blk.clauses += count;
  lglblocking (lgl, lit);
  return count;
}

static void lglsignedmark (LGL * lgl, int lit) {
  AVar * av = lglavar (lgl, lit);
  int bit = 1 << ((lit < 0) ? 1 : 2);
  if (av->mark & bit) return;
  av->mark |= bit;
}

static void lglsignedmarknpushseen (LGL * lgl, int lit) {
  lglsignedmark (lgl, lit);
  lglpushstk (lgl, &lgl->seen, lit);
}

static int lglsignedmarked (LGL * lgl, int lit) {
  AVar * av = lglavar (lgl, lit);
  int bit = 1 << ((lit < 0) ? 1 : 2);
  return av->mark & bit;
}

static int lglhla (LGL * lgl, int start) {
  int next, blit, tag, other, red, lit, tmp;
  const int * p, * w, * eow;
  HTS * hts;
  assert (lglmtstk (&lgl->seen));
  lglsignedmarknpushseen (lgl, start);
  next = 0;
  LOG (3, "starting hidden literal addition from %d", start);
  while (next < lglcntstk (&lgl->seen)) {
    lit = lglpeek (&lgl->seen, next++);
    hts = lglhts (lgl, lit);
    if (!hts->count) continue;
    w = lglhts2wchs (lgl, hts);
    eow = w + hts->count;
    for (p = w; p < eow; p++) {
      lgl->stats.hte.hla.steps++;
      lgl->stats.hte.all.steps++;
      blit = *p;
      tag = blit & MASKCS;
      if (tag == TRNCS || tag == LRGCS) p++;
      if (tag != BINCS) continue;
      red = blit & REDCS;
      if (red) continue;
      other = -(blit >> RMSHFT);
      if (lglsignedmarked (lgl, other)) continue;
      if (lglsignedmarked (lgl, -other)) {
	assert (!lgl->level);
	LOG (1, "failed literal %d in hidden tautology elimination", -start);
	lglunit (lgl, start);
	tmp = lglflush (lgl);
	if (!tmp && !lgl->mt) lgl->mt = 1;
	lgl->stats.hte.failed++;
	return 0;
      }
      LOG (3, "added hidden literal %d", other);
      lglsignedmarknpushseen (lgl, other);
      if (lglcntstk (&lgl->seen) > lgl->limits.hla) return 1;
    }
  }
  return 1;
}

static void lgladdhtebincls (LGL * lgl, int a, int b, int red) {
  assert (lglmtstk (&lgl->clause));
  if (a == -b) return;
  if (lglval (lgl, a) > 0) return;
  if (lglval (lgl, b) > 0) return;
  if (!lglval (lgl, a)) lglpushstk (lgl, &lgl->clause, a);
  if (!lglval (lgl, b)) lglpushstk (lgl, &lgl->clause, b);
  lglpushstk (lgl, &lgl->clause, 0);
  LOG (2, "hte binary clause", a, b);
#ifndef NLGLPICOSAT
  lglpicosatchkcls (lgl);
#endif
  lgladdcls (lgl, red, 0);
  lglclnstk (&lgl->clause);
}

static void lglhte (LGL * lgl) {
  int idx, sign, lit, blit, tag, red, other, other2, lidx, witness;
  int first, pos, delta, nlits, found, changed, success;
  struct { Stk trn, lrg; int count; } taut, rem;
  int64_t limit, oldprgss = lgl->stats.prgss;
  const int * p, * w, * eow, * c, * l;
  HTS * hts;
  assert (lgl->dense);
  nlits = 2*(lgl->nvars - 2);
  if (nlits <= 0) return;
  lglstart (lgl, &lgl->stats.tms.hte);
  lgl->stats.hte.count++;
  CLR (taut.trn); CLR (taut.lrg);
  CLR (rem.trn); CLR (rem.lrg);
  taut.count = rem.count = 0;
  first = 0;
  pos = lglrand (lgl) % nlits;
  delta = lglrand (lgl) % nlits;
  if (!delta) delta++;
  while (lglgcd (delta, nlits) > 1)
    if (++delta == nlits) delta = 1;
  LOG (1, "hte start %u delta %u mod %u", pos, delta, nlits);
  if (lgl->stats.hte.count == 1) limit = lgl->opts.htemaxeff.val/10;
  else limit = (lgl->opts.htereleff.val*lgl->stats.visits.search)/1000;
  if (limit < lgl->opts.htemineff.val) limit = lgl->opts.htemineff.val;
  if (limit > lgl->opts.htemaxeff.val) limit = lgl->opts.htemaxeff.val;
  LOG (2, "hte penalty %d", lgl->limits.hte.pen);
  if (lgl->limits.hte.pen < 0) limit <<= -lgl->limits.hte.pen;
  if (lgl->limits.hte.pen > 0) limit >>= lgl->limits.hte.pen;
  LOG (2, "hte search steps limit %lld", (long long) limit);
  limit += lgl->stats.hte.all.steps;
  changed = 0;
  while (!lgl->mt) {
    if (lgl->stats.hte.all.steps >= limit) break;
    if (lglterminate (lgl)) break;
    if (!lglsyncunits (lgl)) break;
    sign = (pos & 1) ? -1 : 1;
    idx = pos/2 + 2;
    assert (2 <= idx && idx < lgl->nvars);
    lit = sign * idx;
    if (lglval (lgl, lit)) goto CONTINUE;
    if (!lglhla (lgl, lit)) { changed = 1; goto CONTINUE; }
    assert (lglmtstk (&taut.trn));
    assert (lglmtstk (&taut.lrg));
    assert (lglmtstk (&rem.trn));
    assert (lglmtstk (&rem.lrg));
    hts = lglhts (lgl, lit);
    w = lglhts2wchs (lgl, hts);
    eow = w + hts->count;
    for (p = w; p < eow && lgl->stats.hte.all.steps < limit; p++) {
      lgl->stats.hte.cls.steps++;
      lgl->stats.hte.all.steps++;
      blit = *p;
      tag = blit & MASKCS;				/* (1) see lgldense */
      assert (tag != LRGCS);
      if (tag == TRNCS) p++;
      if (tag == BINCS) continue;
      red = blit & REDCS;
      if (red && !lgl->opts.htered.val) continue;
      assert (!red || tag == TRNCS);			/* see (1) */
      if (tag == TRNCS) {
	other = blit >> RMSHFT;
	other2 = *p;
	if (lglsignedmarked (lgl, -other)) {
	  lglpushstk (lgl, &taut.trn, red);
	  lglpushstk (lgl, &taut.trn, other);
	  lglpushstk (lgl, &taut.trn, other2);
	  lglpushstk (lgl, &taut.trn, other);
	} else if (lglsignedmarked (lgl, -other2)) {
	  lglpushstk (lgl, &taut.trn, red);
	  lglpushstk (lgl, &taut.trn, other);
	  lglpushstk (lgl, &taut.trn, other2);
	  lglpushstk (lgl, &taut.trn, other2);
	} else if (lglstr (lgl) && lglsignedmarked (lgl, other)) {
	  lglpushstk (lgl, &rem.trn, red);
	  lglpushstk (lgl, &rem.trn, other);
	  lglpushstk (lgl, &rem.trn, other2);
	  lglpushstk (lgl, &rem.trn, other);
	} else if (lglstr (lgl) && lglsignedmarked (lgl, other2)) {
	  lglpushstk (lgl, &rem.trn, red);
	  lglpushstk (lgl, &rem.trn, other);
	  lglpushstk (lgl, &rem.trn, other2);
	  lglpushstk (lgl, &rem.trn, other2);
	}
      } else {
	assert (!red);					/* see (1) */
	assert (tag == IRRCS);
	lidx = blit >> RMSHFT;
	c = lglidx2lits (lgl, 0, lidx);
	for (l = c; (other = *l); l++) {
	  if (other == lit) continue;
	  if (lglsignedmarked (lgl, -other)) {
	    lglpushstk (lgl, &taut.lrg, lidx);
	    lglpushstk (lgl, &taut.lrg, other);
	    break;
	  }
	  if (lglstr (lgl) && lglsignedmarked (lgl, other)) {
	    lglpushstk (lgl, &rem.lrg, lidx);
	    lglpushstk (lgl, &rem.lrg, other);
	    /* Removing multiple hidden literals at once is tricky
	     * so we simply remove only one at most for one clause
	     * in each round and thus 'break' ...
	     */
	    break;
	  }
	}
      }
    }
    while (!lglmtstk (&taut.lrg)) {
      witness = lglpopstk (&taut.lrg);
      lidx = lglpopstk (&taut.lrg);
      LOGCLS (2, lglidx2lits (lgl, 0, lidx),
              "hidden tautology on %d and %d irredundant large clause",
	      lit, witness);
      lglrmlcls (lgl, lidx, 0);
      lgl->stats.hte.taut.irr.lrg++;
      lgl->stats.prgss++;
      taut.count++;
    }
    while (!lglmtstk (&taut.trn)) {
      witness = lglpopstk (&taut.trn);
      other2 = lglpopstk (&taut.trn);
      other = lglpopstk (&taut.trn);
      red = lglpopstk (&taut.trn);
      LOG (2, "hidden tautology on %d and %d %s ternary clause %d %d %d",
           lit, witness, lglred2str (red), lit, other, other2);
      lglrmtcls (lgl, lit, other, other2, red);
      if (red) lgl->stats.hte.taut.red.trn++;
      else lgl->stats.hte.taut.irr.trn++;
      lgl->stats.prgss++;
      taut.count++;
    }
    while (!lglmtstk (&rem.lrg)) {
      witness = lglpopstk (&rem.lrg);
      lidx = lglpopstk (&rem.lrg);
      LOGCLS (2, lglidx2lits (lgl, 0, lidx),
	"hidden literal removal of %d on %d in irredundant large clause",
	 witness, lit);
      lgl->stats.hte.rem.irr.lrg++;
      lgl->stats.prgss++;
      rem.count++;
      assert (lglmtstk (&lgl->clause));
      c = lglidx2lits (lgl, 0, lidx);
      found = 0;
      for (l = c; (other = *l); l++)
	if (other == witness) found = 1;
	else if (lglval (lgl, other) > 0) break;
	else if (!lglval (lgl, other)) lglpushstk (lgl, &lgl->clause, other);
      if (!other) {
	lglpushstk (lgl, &lgl->clause, 0);
	assert (found);
	lglrmlcls (lgl, lidx, 0);
#ifndef NLGLPICOSAT
	lglpicosatchkcls (lgl);
#endif
	lgladdcls (lgl, 0, 0);			/* but no glue here */
      }
      lglclnstk (&lgl->clause);
    }
    while (!lglmtstk (&rem.trn)) {
      witness = lglpopstk (&rem.trn);
      other2 = lglpopstk (&rem.trn);
      other = lglpopstk (&rem.trn);
      red = lglpopstk (&rem.trn);
      LOG (2,
           "hidden literal removal of %d on %d in %s ternary clause %d %d %d",
	  witness, lit, lglred2str (red), lit, other, other2);
      if (red) lgl->stats.hte.rem.red.trn++;
      else lgl->stats.hte.rem.irr.trn++;
      lgl->stats.prgss++;
      rem.count++;
      lglrmtcls (lgl, lit, other, other2, red);
      lgladdhtebincls (lgl, lit, (other==witness) ? other2 : other, red);
      changed = 1;
    }
CONTINUE:
    lglpopnunmarkstk (lgl, &lgl->seen);
    if (first == lit) {
      if (!changed) break;
      changed = 0;
    }
    if (!first) first = lit;
    pos += delta;
    if (pos >= nlits) pos -= nlits;
  }
  lglprt (lgl, 2, "[hte-%d] %d hidden tautologies and %d literals",
          lgl->stats.hte.count, taut.count, rem.count);
  lglrelstk (lgl, &taut.trn);
  lglrelstk (lgl, &taut.lrg);
  lglrelstk (lgl, &rem.trn);
  lglrelstk (lgl, &rem.lrg);
  lglrep (lgl, 1, 'h');
  lgl->limits.hla += lgl->opts.hlaliminc.val;
  if (lgl->limits.hla > lgl->opts.hlamaxlim.val)
    lgl->limits.hla = lgl->opts.hlamaxlim.val;
  success = oldprgss < lgl->stats.prgss;
  if (success && lgl->limits.hte.pen > MINPEN) lgl->limits.hte.pen--;
  if (!success && lgl->limits.hte.pen < MAXPEN) lgl->limits.hte.pen++;
  lglstop (lgl);
}

static void lglblock (LGL * lgl) {
  Stk blocked[5];
  int idx, count;
  int64_t limit;
  assert (lglsmall (lgl));
  assert (lgl->simp);
  assert (lgl->dense);
  assert (lgl->eliminating);
  assert (!lgl->blocking);
  assert (!lgl->elm.pivot);
  assert (!lgl->level);
  lglstart (lgl, &lgl->stats.tms.blk);
  lgl->blocking = 1;
  lgl->stats.blk.rounds++;
  count = 0;
  memset (blocked, 0, sizeof blocked);
  if (lgl->stats.blk.rounds == 1) limit = lgl->opts.blkmaxeff.val/10;
  else limit = (lgl->opts.blkreleff.val*lgl->stats.visits.search)/1000;
  if (limit < lgl->opts.blkmineff.val) limit = lgl->opts.blkmineff.val;
  if (limit > lgl->opts.blkmaxeff.val) limit = lgl->opts.blkmaxeff.val;
  LOG (1, "blocking resolution steps limit %lld", (long long) limit);
  limit += lgl->stats.blk.res;
  while (!lglterminate (lgl) &&
         lgl->stats.blk.res < limit &&
         !lglmtstk (&lgl->esched)) {
    // TODO use 'itimer' instead
    if (lgl->opts.verbose.val > 2) {
      printf ("c k clauses %d, schedule %ld, limit %lld",
              lgl->stats.irr,
	      (long) lglcntstk (&lgl->esched),
	      (long long)(limit - lgl->stats.blk.res));
      printf (isatty (1) ? "                 \r" : "\n");
      fflush (stdout);
    }
    idx = lglpopesched (lgl);
    lgl->elm.pivot = idx;
    count += lglblocklit (lgl, idx, blocked);
    count += lglblocklit (lgl, -idx, blocked);
  }
  lglrelstk (lgl, blocked+2);
  lglrelstk (lgl, blocked+3);
  lglrelstk (lgl, blocked+4);
  lgl->elm.pivot = 0;
  LOG (1, "blocked clause elimination of %d clauses", count);
  assert (lgl->blocking);
  lgl->blocking = 0;
  lgleschedall (lgl);
  lglstop (lgl);
  lglrep (lgl, 1, 'k');
  assert (!lgl->mt);
}

static DFPR * lglstampall (LGL *, int);

static int lglelim (LGL * lgl) {
  int res = 1, idx, elmd, relelmd, oldnvars, skip, oldelmd;
  int round, flushed, success;
  int64_t limit, oldprgss;
  DFPR * dfpr;
  assert (lgl->opts.elim.val);
  oldnvars = lgl->nvars;
  skip = (!oldnvars || !lglsmall (lgl));
  if (skip) { lgl->stats.elm.skipped++; goto DONE; }
  if (lgl->mt || lgl->nvars <= 2) goto DONE;
  lgl->stats.elm.count++;
  lglstart (lgl, &lgl->stats.tms.elm);
  assert (!lgl->eliminating);
  assert (!lgl->simp);
  lgl->eliminating = 1;
  lgl->simp = 1;
  lglgc (lgl);
  if (lgl->level > 0) lglbacktrack (lgl, 0);
  lglfreezer (lgl);
  lgldense (lgl);
  if (lgl->opts.hte.val) { lglhte (lgl); res = !lgl->mt; }
  if (res && lgl->opts.block.val) lglblock (lgl);
  round = 1;
  LOG (2, "current elimination excess %d", lgl->limits.elm.excess);
  if (lgl->stats.elm.count == 1) limit = lgl->opts.elmaxeff.val/10;
  else limit = (lgl->opts.elmreleff.val*lgl->stats.visits.search)/1000;
  if (limit < lgl->opts.elmineff.val) limit = lgl->opts.elmineff.val;
  if (limit > lgl->opts.elmaxeff.val) limit = lgl->opts.elmaxeff.val;
  LOG (2, "elimination penalty %d", lgl->limits.elm.pen);
  if (lgl->limits.elm.pen < 0) limit <<= -lgl->limits.elm.pen;
  if (lgl->limits.elm.pen > 0) limit >>= lgl->limits.elm.pen;
  LOG (2, "elimination up to %lld subsumption checks / resolutions", limit);
  lgl->limits.elm.steps = lgl->stats.elm.steps + limit;
  oldelmd = lgl->stats.elm.elmd;
  oldprgss = lgl->stats.prgss;
  lgl->stats.elm.rounds++;
  if (res && 
      (res = lglflush (lgl)) && 
      lgl->opts.elmhte.val &&
      !lglstr (lgl)) {
    dfpr = lglstampall (lgl, 1);
    res = lglflush (lgl);
  } else dfpr = 0;
  flushed = 0;
  while (res &&
	 !lglterminate (lgl) &&
         !(flushed = lglmtstk (&lgl->esched)) &&
	 lgl->limits.elm.steps > lgl->stats.elm.steps) {
    // TODO use 'itimer' instead
    if (lgl->opts.verbose.val > 2) {
      printf ("c e %d variables, schedule %ld, limit %lld",
              lglrem (lgl) - (lgl->stats.elm.elmd - oldelmd),
	      (long) lglcntstk (&lgl->esched),
	      (long long)(limit - lgl->stats.elm.steps));
      printf (isatty (1) ? "                 \r" : "\n");
      fflush (stdout);
    }
    idx = lglpopesched (lgl);
    lglelimlit (lgl, dfpr, idx);
    res = lglflush (lgl);
  }
  if (dfpr) DEL (dfpr, 2*lgl->nvars);
  lglrelecls (lgl);
  lglsparse (lgl);
  if (res) { lglgc (lgl); if (lgl->mt) res = 0; } else assert (lgl->mt);
  elmd = oldnvars - lgl->nvars;
  relelmd = (100*elmd) / oldnvars;
  success = oldprgss < lgl->stats.prgss;
  if (success && lgl->limits.elm.pen > MINPEN) lgl->limits.elm.pen--;
  if (!success && lgl->limits.elm.pen < MAXPEN) lgl->limits.elm.pen++;
  lglprt (lgl, 2,
          "%ssuccessfully eliminated %d = %d%% variables out of %d",
	  success ? "" : "un", elmd, relelmd, oldnvars);
  assert (lgl->eliminating);
  assert (lgl->simp);
  lgl->eliminating = 0;
  lgl->simp = 0;
  lglrep (lgl, 1, 'e');
  lglstop (lgl);
DONE:
  lgl->limits.elm.vinc += lgl->opts.elmvintinc.val;
  lgl->limits.elm.cinc += lgl->opts.elmcintinc.val;
  lgl->limits.elm.visits = lgl->stats.visits.search + lgl->limits.elm.vinc;
  lgl->limits.elm.confs = lgl->stats.confs + lgl->limits.elm.cinc;
  lgl->limits.elm.irr = lgl->stats.irr + lgl->opts.elmirrintinc.val;
  lgl->limits.elm.prgss = lgl->stats.prgss;
  assert (res || lgl->mt);
  return res;
}

static int lglelitblockingoreliminated (LGL * lgl, int elit) {
  Ext * ext = lglelit2ext (lgl, elit);
  return ext->blocking || ext->eliminated;
}

static int lglsynceqs (LGL * lgl) {
  int * ereprs, * ireprs, emax = lgl->maxext;
  int elit1, erepr1, elit2, erepr2;
  int ilit1, irepr1, ilit2, irepr2;
  int consumed = 0, produced = 0;
  assert (!lgl->mt);
  assert (!lgl->level);
  if (!lgl->nvars) return 1;
  assert (lgl->repr);
  if (!lgl->eqs.lock.fun) return 1;
  ereprs = lgl->eqs.lock.fun (lgl->eqs.lock.state);
  ireprs = lgl->repr;
  produced = consumed = 0;
  for (elit1 = 1; elit1 <= emax; elit1++) {
    if (lglelitblockingoreliminated (lgl, elit1)) continue;
    elit2 = lglptrjmp (ereprs, emax, elit1);
    if (elit2 == elit1) continue;
    if (lglelitblockingoreliminated (lgl, elit2)) continue;
    assert (elit2 != -elit1);
    erepr1 = lglerepr (lgl, elit1);
    if (lglelitblockingoreliminated (lgl, erepr1)) continue;
    erepr2 = lglerepr (lgl, elit2);
    if (lglelitblockingoreliminated (lgl, erepr2)) continue;
    if (erepr1 == erepr2) continue;
    if (erepr1 == -erepr2) {
INCONSISTENT:
      LOG (1, "inconsistent external equivalence %d %d", elit1, elit2);
      assert (!lgl->level);
      lgl->mt = 1;
      goto DONE;
    }
    ilit1 = lglimport (lgl, elit1);
    ilit2 = lglimport (lgl, elit2);
    if (ilit1 == ilit2) continue;
    if (ilit1 == -ilit2) goto INCONSISTENT;
    if (abs (ilit1) <= 1) continue;
    if (abs (ilit2) <= 1) continue;
    irepr1 = lglirepr (lgl, ilit1);
    irepr2 = lglirepr (lgl, ilit2);
    if (irepr1 == irepr2) continue;
    if (irepr1 == -irepr2) goto INCONSISTENT;
    if (abs (irepr1) <= 1) continue;
    if (abs (irepr2) <= 1) continue;
    LOG (2, "importing external equivalence %d %d as internal %d %d",
         elit1, elit2, irepr1, irepr2);
    // TODO irepr1 and/or irepr2 assigned ...
    if (!lglisfree (lgl, irepr1)) continue;
    if (!lglisfree (lgl, irepr2)) continue;
    consumed++;
    lglimerge (lgl, irepr1, irepr2);
  }
  LOG (1, "consumed %d equivalences", consumed);
  for (elit1 = 1; elit1 <= emax; elit1++) {
    elit2 = lglerepr (lgl, elit1);
    if (elit1 == elit2) continue;
    assert (elit1 != -elit2);
    erepr1 = lglptrjmp (ereprs, emax, elit1);
    erepr2 = lglptrjmp (ereprs, emax, elit2);
    if (erepr1 == erepr2) continue;
    assert (erepr1 != -erepr2);
    LOG (2, "exporting external equivalence %d %d", erepr1, erepr2);
    produced++;
    ereprs[abs (erepr1)] = (erepr1 < 0) ? -erepr2 : erepr2;
  }
  LOG (1, "produced %d equivalences", produced);
DONE:
  if (lgl->eqs.unlock.fun) 
    lgl->eqs.unlock.fun (lgl->eqs.unlock.state, consumed, produced);
  return !lgl->mt;
}

static int lgldecomp (LGL * lgl) {
  int res = 1;
  if (!lglsmall (lgl)) goto NEXT;
  if (!lglmyturn (lgl, lgl->stats.decomps++)) goto NEXT;
  assert (lgl->opts.decompose.val);
  assert (!lgl->decomposing);
  lglstart (lgl, &lgl->stats.tms.dcp);
  lgl->decomposing = 1;
  assert (!lgl->simp);
  lgl->simp = 1;
  if (lgl->level > 0) lglbacktrack (lgl, 0);
  res = 0;
  if (!lglbcp (lgl)) goto DONE;
  lglgc (lgl);
  if (lgl->mt) goto DONE;
  if (!lgltarjan (lgl)) goto DONE;
  if (!lglsynceqs (lgl)) goto DONE;
  lglchkred (lgl);
  lgldcpdis (lgl);
  lgldcpcln (lgl);
  lgldcpcon (lgl);
  lglfitlirs (lgl);
  lgldreschedule (lgl);
  lglmap (lgl);
  if (lgl->mt) goto DONE;
  if (!lglbcp (lgl)) goto DONE;
  lglcount (lgl);
  lglgc (lgl);
  if (lgl->mt) goto DONE;
  lgldreschedule (lgl);
  if (!lgl->mt) { lglpicosatchkall (lgl); lglpicosatrestart (lgl); }
  res = 1;
DONE:
  assert (lgl->decomposing);
  lgl->decomposing = 0;
  assert (lgl->simp);
  lgl->simp = 0;
  lglstop (lgl);
  lglrep (lgl, 1, 'd');
NEXT:
  lgl->limits.dcp.vinc += lgl->opts.dcpvintinc.val;
  lgl->limits.dcp.cinc += lgl->opts.dcpcintinc.val;
  lgl->limits.dcp.visits = lgl->stats.visits.search + lgl->limits.dcp.vinc;
  lgl->limits.dcp.confs = lgl->stats.confs + lgl->limits.dcp.cinc;
  lgl->limits.dcp.irr = lgl->stats.irr + lgl->opts.dcpirrintinc.val;
  lgl->limits.dcp.prgss = lgl->stats.prgss;
  return res;
}

static int lglrandomprobe (LGL * lgl, Stk * outer) {
  unsigned pos, mod;
  int res;
  mod = lglcntstk (outer);
  if (!mod) return 0;
  pos = lglrand (lgl) % mod;
  res = lglpeek (outer, pos);
  if (lglval (lgl, res)) return 0;
  assert (res == abs (res));
  return res;
}

static int lglinnerprobe (LGL * lgl, int old,  Stk * outer, Stk * tmp) {
  int i, lit, blit, tag, other, other2, res;
  const int * w, * eow, * p;
  HTS * hts;
  assert (old < lglcntstk (&lgl->trail));
  assert (lglmtstk (tmp));
  for (i = old; i < lglcntstk (&lgl->trail); i++) {
    lit = lglpeek (&lgl->trail, i);
    hts = lglhts (lgl, -lit);
    w = lglhts2wchs (lgl, hts);
    eow = w + hts->count;
    for (p = w; p < eow; p++) {
      blit = *p;
      tag = blit & MASKCS;
      if (tag == TRNCS || tag == LRGCS) p++;
      if (tag == BINCS || tag == LRGCS) continue;
      assert (tag == TRNCS);
      other = blit >> RMSHFT;
      if (lglval (lgl, other) > 0) continue;
      other2 = *p;
      if (lglval (lgl, other2) > 0) continue;
      assert (!lglval (lgl, other));
      assert (!lglval (lgl, other2));
      other = abs (other);
      if (!lglmarked (lgl, other)) {
	lglmark (lgl, other);
	lglpushstk (lgl, tmp, other);
	LOG (4, "potential inner probe %d for %d", other, lit);
      }
      other2 = abs (other2);
      if (!lglmarked (lgl, other2)) {
	lglmark (lgl, other2);
	lglpushstk (lgl, tmp, other2);
	LOG (3, "potential inner probe %d for %d", other2, lit);
      }
    }
  }
  LOG (0, "found %d inner probes in ternary clauses", lglcntstk (tmp));
  res = lglrandomprobe (lgl, tmp);
  lglpopnunmarkstk (lgl, tmp);
  if (!res) res = lglrandomprobe (lgl, outer);
  return res;
}

static void lglcleanrepr (LGL * lgl, Stk * represented, int * repr) {
  int idx;
  while (!lglmtstk (represented)) {
    idx = lglpopstk (represented);
    assert (2 <= idx && idx < lgl->nvars);
    assert (repr[idx]);
    repr[idx] = 0;
  }
}

static void lgladdliftbincls (LGL * lgl, int a, int b) {
  assert (lgl->lifting);
  assert (lglmtstk (&lgl->clause));
  lglpushstk (lgl, &lgl->clause, a);
  lglpushstk (lgl, &lgl->clause, b);
  lglpushstk (lgl, &lgl->clause, 0);
  LOG (2, "lifted binary clause", a, b);
#ifndef NLGLPICOSAT
  lglpicosatchkcls (lgl);
#endif
  lgladdcls (lgl, REDCS, 0);
  lglclnstk (&lgl->clause);
  lgl->stats.lift.impls++;
}

static int lgliftaux (LGL * lgl) {
  int i, idx, lit, * reprs[3], first, outer, inner, changed, branch;
  int ok, oldouter, oldinner, dom, repr, other;
  int lit1, lit2, repr1, repr2, orepr1, orepr2;
  Stk probes, represented[2], saved, tmp;
  unsigned pos, delta, mod;
  Val val, val1, val2;
  int64_t limit;
  assert (lgl->simp && lgl->lifting && !lgl->level);
  NEW (lgl->repr, lgl->nvars);
  if (lgl->stats.lift.count == 1) limit = lgl->opts.lftmaxeff.val/10;
  else limit = (lgl->opts.lftreleff.val*lgl->stats.visits.search)/1000;
  if (limit < lgl->opts.lftmineff.val) limit = lgl->opts.lftmineff.val;
  if (limit > lgl->opts.lftmaxeff.val) limit = lgl->opts.lftmaxeff.val;
  LOG (0, "lifting with penalty %d", lgl->limits.lft.pen);
  if (lgl->limits.lft.pen < 0) limit <<= -lgl->limits.lft.pen;
  if (lgl->limits.lft.pen > 0) limit >>= lgl->limits.lft.pen;
  LOG (0, "lifting with up to %lld propagations", (long long) limit);
  limit += lgl->stats.visits.simp;
  CLR (probes); CLR (saved); CLR (tmp);
  CLR (represented[0]); CLR (represented[1]);
  NEW (reprs[0], lgl->nvars);
  NEW (reprs[1], lgl->nvars);
  NEW (reprs[2], lgl->nvars);
  for (idx = 2; idx < lgl->nvars; idx++) {
    if (!lglisfree (lgl, idx)) continue;
    LOG (1, "new outer probe %d", idx);
    lglpushstk (lgl, &probes, idx);
  }
  mod = lglcntstk (&probes);
  if (!(mod)) goto DONE;
  LOG (0, "found %u active outer probes out of %d variables %.1f%%",
       mod, lgl->nvars - 1, lglpcnt (mod, lgl->nvars-1));
  pos = lglrand (lgl)  % mod;
  delta = lglrand (lgl) % mod;
  if (!delta) delta++;
  while (lglgcd (delta, mod) > 1)
    if (++delta == mod) delta = 1;
  LOG (0, "lifting start %u delta %u mod %u", pos, delta, mod);
  changed = first = 0;
  assert (lgl->simp);
  while (!lgl->mt) {
    if (lgl->stats.visits.simp >= limit) break;
    if (lglterminate (lgl)) break;
    if (!lglsyncunits (lgl)) break;
    assert (pos < (unsigned) mod);
    outer = probes.start[pos];
    if (outer == first) { if (changed) changed = 0; else break; }
    if (!first) first = outer;
    pos += delta;
    if (pos >= mod) pos -= mod;
    if (lglval (lgl, outer)) continue;
    lgl->stats.lift.probed[0]++;
    LOG (0, "1st outer branch %d during lifting", outer);
    oldouter = lglcntstk (&lgl->trail);
    lgliassume (lgl, outer);
    ok = lglbcp (lgl);
    if (!ok) {
FIRST_OUTER_BRANCH_FAILED:
      dom = lglprbana (lgl, outer);
      LOG (0, "1st outer branch failed literal %d during lifting", outer);
      lgl->stats.lift.units++;
      lglbacktrack (lgl, 0);
      lglunit (lgl, -dom);
      if (lglbcp (lgl)) continue;
      LOG (0, "empty clause after propagating outer probe during lifting");
      assert (!lgl->mt);
      lgl->mt = 1;
      break;
    }
    inner = lglinnerprobe (lgl, oldouter, &probes, &tmp);
    assert (lglmtstk (&represented[0]));
    if (!inner) {
FIRST_OUTER_BRANCH_WIHOUT_INNER_PROBE:
      LOG (0, "no inner probe for 1st outer probe %d", outer);
      for (i = oldouter; i < lglcntstk (&lgl->trail); i++) {
	lit = lglpeek (&lgl->trail, i);
	idx = abs (lit);
	assert (!reprs[0][idx]);
	reprs[0][idx] = lglsgn (lit);
	lglpushstk (lgl, &represented[0], idx);
      }
      assert (lgl->level == 1);
      goto END_OF_FIRST_OUTER_BRANCH;
    } 
    oldinner = lglcntstk (&lgl->trail);
    LOG (0, "1st inner branch %d in outer 1st branch %d", inner, outer);
    lgl->stats.lift.probed[1]++;
    lgliassume (lgl, inner);
    ok = lglbcp (lgl);
    if (!ok) {
      LOG (0, "1st inner branch failed literal %d on 1st outer branch %d",
          inner, outer);
      lglbacktrack (lgl, 1);
      assert (lglcntstk (&lgl->trail) == oldinner);
      lgladdliftbincls (lgl, -inner, -outer);
      assert (lglcntstk (&lgl->trail) == oldinner + 1);
      ok = lglbcp (lgl);
      if (ok) goto FIRST_OUTER_BRANCH_WIHOUT_INNER_PROBE;
      LOG (0, "conflict after propagating negation of 1st inner branch");
      goto FIRST_OUTER_BRANCH_FAILED;
    }
    lglclnstk (&saved);
    for (i = oldouter; i < lglcntstk (&lgl->trail); i++)
      lglpushstk (lgl, &saved, lglpeek (&lgl->trail, i));
    LOG (0, "saved %d assignments of 1st inner branch %d in 1st outer branch", 
	 lglcntstk (&saved), inner, outer);
    lglbacktrack (lgl, 1);
    assert (lglcntstk (&lgl->trail) == oldinner);
    LOG (0, "2nd inner branch %d in 1st outer branch %d", -inner, outer);
    lgl->stats.lift.probed[1]++;
    lgliassume (lgl, -inner);
    ok = lglbcp (lgl);
    if (!ok) {
      LOG (0, "2nd inner branch failed literal %d on 1st outer branch %d",
           -inner, outer);
      lglbacktrack (lgl, 1);
      assert (lglcntstk (&lgl->trail) == oldinner);
      lgladdliftbincls (lgl, inner, -outer);
      assert (lglcntstk (&lgl->trail) == oldinner + 1);
      ok = lglbcp (lgl);
      if (ok) goto FIRST_OUTER_BRANCH_WIHOUT_INNER_PROBE;
      LOG (0, "conflict after propagating negation of 2nd inner branch");
      goto FIRST_OUTER_BRANCH_FAILED;
    } 
    while (!lglmtstk (&saved)) {
      lit = lglpopstk (&saved);
      idx = abs (lit);
      val1 = lglsgn (lit);
      val2 = lglval (lgl, idx);
      if (val1 == val2) {
	assert (!reprs[0][idx]);
	reprs[0][idx] = val1;
	lglpushstk (lgl, &represented[0], idx);
      } else if (lit != inner && val1 == -val2) {
	assert (lit != -inner);
	repr = lglptrjmp (reprs[0], lgl->nvars-1, inner);
	other = lglptrjmp (reprs[0], lgl->nvars-1, lit);
	if (lglcmprepr (lgl, other, repr) < 0) SWAP (repr, other);
	if (other < 0) other = -other, repr = -repr;
	assert (!reprs[0][other]);
	reprs[0][other] = repr;
	lglpushstk (lgl, &represented[0], other);
      } else assert (lit == inner || !val2);
    }
    lglbacktrack (lgl, 1);
END_OF_FIRST_OUTER_BRANCH:
    assert (lgl->level == 1);
#ifndef NLGLOG
    {
      LOG (0, "start of 1st outer branch %d equivalences:", outer);
      for (i = 0; i < lglcntstk (&represented[0]); i++) {
	other = lglpeek (&represented[0], i);
	repr = reprs[0][other];
	LOG (0, "  1st branch equivalence %d : %d = %d", i + 1, other, repr);
      }
      LOG (0, "end of 1st outer branch %d equivalences.", outer);
    }
#endif
    lglbacktrack (lgl, 0);
    assert (lglcntstk (&lgl->trail) == oldouter);
    lgl->stats.lift.probed[0]++;
    LOG (0, "2nd outer branch %d during lifting", -outer);
    lgliassume (lgl, -outer);
    ok = lglbcp (lgl);
    if (!ok) {
SECOND_OUTER_BRANCH_FAILED:
      dom = lglprbana (lgl, -outer);
      LOG (0, "2nd branch outer failed literal %d during lifting", -outer);
      lgl->stats.lift.units++;
      lglbacktrack (lgl, 0);
      lglunit (lgl, -dom);
      if (lglbcp (lgl)) goto CONTINUE;
      assert (!lgl->mt);
      lgl->mt = 1;
      goto CONTINUE;
    }
    assert (lglmtstk (&represented[1]));
    oldinner = lglcntstk (&lgl->trail);
    if (!inner || lglval (lgl, inner)) 
      inner = lglinnerprobe (lgl, oldouter, &probes, &tmp);
    if (!inner) {
SECOND_OUTER_BRANCH_WIHOUT_INNER_PROBE:
      LOG (0, "no inner probe for 2nd outer branch %d", -outer);
      for (i = oldouter; i < lglcntstk (&lgl->trail); i++) {
	lit = lglpeek (&lgl->trail, i);
	idx = abs (lit);
	assert (!reprs[1][idx]);
	reprs[1][idx] = lglsgn (lit);
	lglpushstk (lgl, &represented[1], idx);
      }
      assert (lgl->level == 1);
      goto END_OF_SECOND_BRANCH;
    }
    LOG (0, "1st inner branch %d in outer 2nd branch %d", inner, -outer);
    lgl->stats.lift.probed[1]++;
    lgliassume (lgl, inner);
    ok = lglbcp (lgl);
    if (!ok) {
      LOG (0, "1st inner branch failed literal %d on 2nd outer branch %d",
           inner, -outer);
      lglbacktrack (lgl, 1);
      assert (lglcntstk (&lgl->trail) == oldinner);
      lgladdliftbincls (lgl, -inner, outer);
      assert (lglcntstk (&lgl->trail) == oldinner + 1);
      ok = lglbcp (lgl);
      if (ok) goto SECOND_OUTER_BRANCH_WIHOUT_INNER_PROBE;
      LOG (0, "conflict after propagating negation of 1st inner branch");
      goto SECOND_OUTER_BRANCH_FAILED;
    }
    lglclnstk (&saved);
    for (i = oldouter; i < lglcntstk (&lgl->trail); i++)
      lglpushstk (lgl, &saved, lglpeek (&lgl->trail, i));
    LOG (0, 
         "saved %d assignments of 1st inner branch %d in 2nd outer branch %d",
	 lglcntstk (&saved), inner, -outer);
    lglbacktrack (lgl, 1);
    assert (lglcntstk (&lgl->trail) == oldinner);
    LOG (0, "2nd inner branch %d in 2nd outer branch %d", -inner, -outer);
    lgl->stats.lift.probed[1]++;
    lgliassume (lgl, -inner);
    ok = lglbcp (lgl);
    if (!ok) {
      LOG (0, "2nd inner branch failed literal %d on 2nd outer branch %d",
           -inner, -outer);
      lglbacktrack (lgl, 1);
      assert (lglcntstk (&lgl->trail) == oldinner);
      lgladdliftbincls (lgl, inner, outer);
      assert (lglcntstk (&lgl->trail) == oldinner + 1);
      ok = lglbcp (lgl);
      if (ok) goto SECOND_OUTER_BRANCH_WIHOUT_INNER_PROBE;
      LOG (0, "conflict after propagating negation of 2nd inner branch");
      goto SECOND_OUTER_BRANCH_FAILED;
    }
    while (!lglmtstk (&saved)) {
      lit = lglpopstk (&saved);
      idx = abs (lit);
      val1 = lglsgn (lit);
      val2 = lglval (lgl, idx);
      if (val1 == val2) {
	assert (!reprs[1][idx]);
	reprs[1][idx] = val1;
	lglpushstk (lgl, &represented[1], idx);
      } else if (lit != inner && val1 == -val2) {
	assert (lit != -inner);
	repr = lglptrjmp (reprs[1], lgl->nvars-1, inner);
	other = lglptrjmp (reprs[1], lgl->nvars-1, lit);
	if (lglcmprepr (lgl, other, repr) < 0) SWAP (repr, other);
	if (other < 0) other = -other, repr = -repr;
	assert (!reprs[1][other]);
	reprs[1][other] = repr;
	lglpushstk (lgl, &represented[1], other);
      } else assert (lit == inner || !val2);
    }
    lglbacktrack (lgl, 1);
END_OF_SECOND_BRANCH:
    assert (lgl->level == 1);
#ifndef NLGLOG
    {
      LOG (0, "start of 2nd outer branch %d equivalences:", -outer);
      for (i = 0; i < lglcntstk (&represented[1]); i++) {
	other = lglpeek (&represented[1], i);
	repr = reprs[1][other];
	LOG (0, "  2nd branch equivalence %d : %d = %d", i + 1, other, repr);
      }
      LOG (0, "end of 2nd outer branch %d equivalences.", outer);
    }
#endif
    lglbacktrack (lgl, 0);
    for (branch = 0; branch <= 1; branch++) {
      assert (lglptrjmp (reprs[!branch], lgl->nvars-1, 1) == 1);
      assert (lglptrjmp (reprs[!branch], lgl->nvars-1, -1) == -1);
      for (i = 0; i < lglcntstk (&represented[branch]); i++) {
	lit1 = lglpeek (&represented[branch], i);
	assert (2 <= lit1 && lit1 < lgl->nvars);
	lit2 = reprs[branch][lit1];
	assert (lit2);
	if (abs (lit2) == 1) {
	  val = lglval (lgl, lit1);
	  assert (!val || val == lit2);
	  if (val) continue;
	  repr1 = lglptrjmp (reprs[!branch], lgl->nvars-1, lit1);
	  if (repr1 != lit2) continue;
	  LOG (0, "  common constant equivalence : %d = %d  (branch %d)",
	       lit1, lit2, branch);
	  lglunit (lgl, lit2*lit1);
	  lgl->stats.lift.units++;
	} else {
	  repr1 = lglptrjmp (reprs[2], lgl->nvars-1, lit1);
	  repr2 = lglptrjmp (reprs[2], lgl->nvars-1, lit2);
	  if (repr1 == repr2) continue;
	  orepr1 = lglptrjmp (reprs[!branch], lgl->nvars-1, lit1);
	  orepr2 = lglptrjmp (reprs[!branch], lgl->nvars-1, lit2);
	  if (orepr1 != orepr2) continue;
	  assert (abs (repr1) > 1 && abs (repr2) > 1);
	  if (lglcmprepr (lgl, repr2, repr1) < 0) SWAP (repr1, repr2);
	  if (repr2 < 0) repr2 = -repr2, repr1 = -repr1;
	  LOG (0, "  common equivalence candidate : %d = %d   (branch %d)", 
	       repr2, repr1, branch);
#if 0
	  lgl->stats.lift.eqs++;
	  lglimerge (lgl, repr2, repr1);
#else
	  reprs[2][repr2] = repr1;
#endif
	}
      }
    }
    lglbcp (lgl);
CONTINUE:
    lglbacktrack (lgl, 0);
    lglcleanrepr (lgl, &represented[0], reprs[0]);
    lglcleanrepr (lgl, &represented[1], reprs[1]);
  }
#if 1
  if (!lgl->mt) {
    for (idx = 2; idx < lgl->nvars; idx++)
      (void) lglptrjmp (reprs[2], lgl->nvars-1, idx);
    for (idx = 2; idx < lgl->nvars; idx++) {
      repr = lglptrjmp (reprs[2], lgl->nvars-1, idx);
      val = lglval (lgl, idx);
      if (!val) continue;
      if (repr == -val) {
	LOG (0, "inconsistent assigned members of equivalence classe");
	lgl->mt = 1;
	goto DONE;
      }
      if (repr < 0) repr = -repr, val = -val;
      if (repr == 1) { assert (val == 1); continue; }
      reprs[2][repr] = val;
    }
    for (idx = 2; idx < lgl->nvars; idx++) {
      repr = lglptrjmp (reprs[2], lgl->nvars-1, idx);
      assert (repr);
      assert (repr != -idx);
      if (repr == idx) continue;
      if (abs (repr) == 1) continue;
      lgl->stats.lift.eqs++;
      LOG (0, "  real common equivalence : %d = %d", idx, repr);
      lglimerge (lgl, idx, repr);
    }
  }
#endif
DONE:
  assert (!lgl->level);
  DEL (reprs[0], lgl->nvars);
  DEL (reprs[1], lgl->nvars);
  DEL (reprs[2], lgl->nvars);
  lglrelstk (lgl, &probes);
  lglrelstk (lgl, &represented[0]);
  lglrelstk (lgl, &represented[1]);
  lglrelstk (lgl, &saved);
  lglrelstk (lgl, &tmp);
  if (lgl->mt) DEL (lgl->repr, lgl->nvars);
  return !lgl->mt;
}

static int lglift (LGL * lgl) {
  int64_t oldprgss = lgl->stats.prgss;
  int success;
  if (!lglsmall (lgl)) goto NEXT;
  if (!lglmyturn (lgl, lgl->stats.lift.count++)) goto NEXT;
  assert (lgl->opts.lift.val);
  assert (!lgl->lifting);
  lglstart (lgl, &lgl->stats.tms.lft);
  lgl->lifting = 1;
  assert (!lgl->simp);
  lgl->simp = 1;
  if (lgl->level > 0) lglbacktrack (lgl, 0);
  if (!lglbcp (lgl)) goto DONE;
  lglgc (lgl);
  if (lgl->mt) goto DONE;
  if (!lgliftaux (lgl)) { assert (lgl->mt); goto DONE; }
  if (!lglsynceqs (lgl)) { assert (lgl->mt); goto DONE; }
  lglchkred (lgl);
  lgldcpdis (lgl);
  lgldcpcln (lgl);
  lgldcpcon (lgl);
  lglfitlirs (lgl);
  lgldreschedule (lgl);
  lglmap (lgl);
  if (lgl->mt) goto DONE;
  if (!lglbcp (lgl)) goto DONE;
  lglcount (lgl);
  lglgc (lgl);
  if (lgl->mt) goto DONE;
  lgldreschedule (lgl);
  if (!lgl->mt) { lglpicosatchkall (lgl); lglpicosatrestart (lgl); }
  success = (lgl->stats.prgss > oldprgss);
  if (success && lgl->limits.lft.pen > MINPEN) lgl->limits.lft.pen--;
  if (!success && lgl->limits.lft.pen < MAXPEN) lgl->limits.lft.pen++;
DONE:
  assert (lgl->lifting);
  lgl->lifting = 0;
  assert (lgl->simp);
  lgl->simp = 0;
  lglrep (lgl, 1, '^');
  lglstop (lgl);
NEXT:
  lgl->limits.lft.vinc += lgl->opts.lftvintinc.val;
  lgl->limits.lft.cinc += lgl->opts.lftcintinc.val;
  lgl->limits.lft.visits = lgl->stats.visits.search + lgl->limits.lft.vinc;
  lgl->limits.lft.confs = lgl->stats.confs + lgl->limits.lft.cinc;
  lgl->limits.lft.irr = lgl->stats.irr + lgl->opts.lftirrintinc.val;
  lgl->limits.lft.prgss = lgl->stats.prgss;
  return !lgl->mt;
}

static void lgldstpull (LGL * lgl, int lit) {
  AVar * av;
  av = lglavar (lgl, lit);
  assert ((lit > 0) == av->wasfalse);
  if (av->mark) return;
  if (!lglevel (lgl, lit)) return;
  av->mark = 1;
  if (lgldecision (lgl, lit)) {
    lglpushstk (lgl, &lgl->clause, lit);
    LOG (3, "added %d to learned clause", lit);
  } else {
    lglpushstk (lgl, &lgl->seen, -lit);
    LOG (3, "pulled in distillation literal %d", -lit);
  }
}

static int lgldstanalit (LGL * lgl, int lit) {
  int r0, r1, antecedents, other, next, tag, * p, * rsn;
  AVar * av;
  assert (lglmtstk (&lgl->seen));
  assert (lglmtstk (&lgl->clause));
  antecedents = 1;
  av = lglavar (lgl, lit);
  rsn = lglrsn (lgl, lit);
  r0 = rsn[0], r1 = rsn[1];
  LOGREASON (2, lit, r0, r1,
             "starting literal distillation analysis for %d with", lit);
  LOG (3, "added %d to learned clause", lit);
  lglpushstk (lgl, &lgl->clause, lit);
  assert ((lit < 0) == av->wasfalse);
  assert (!av->mark);
  av->mark = 1;
  next = 0;
  for (;;) {
    tag = r0 & MASKCS;
    if (tag == BINCS || tag == TRNCS) {
      other = r0 >> RMSHFT;
      lgldstpull (lgl, other);
      if (tag == TRNCS) lgldstpull (lgl, r1);
    } else {
      assert (tag == LRGCS);
      for (p = lglidx2lits (lgl, (r0 & REDCS), r1); (other = *p); p++)
	if (other != lit) lgldstpull (lgl, *p);
    }
    if (next == lglcntstk (&lgl->seen)) break;
    lit = lglpeek (&lgl->seen, next++);
    av = lglavar (lgl, lit);
    assert ((lit < 0) == av->wasfalse);
    rsn = lglrsn (lgl, lit);
    r0 = rsn[0], r1 = rsn[1];
    LOGREASON (2, lit, r0, r1, "literal distillation analysis of");
    antecedents++;
  }
  lglpopnunmarkstk (lgl, &lgl->seen);
  LOG (2, "literal distillation analysis used %d antecedents", antecedents);
  assert (lglcntstk (&lgl->clause) >= 2);
  return antecedents;
}

static int lgldstanaconf (LGL * lgl) {
  int lit, r0, r1, unit, other, next, tag, * p, * rsn;
  AVar * av;
  assert (lgl->conf.lit);
  assert (lglmtstk (&lgl->seen));
  assert (lglmtstk (&lgl->clause));
  lit = lgl->conf.lit, r0 = lgl->conf.rsn[0], r1 = lgl->conf.rsn[1];
  LOGREASON (2, lit, r0, r1,
             "starting conflict distillation analysis for %d with", lit);
  lgldstpull (lgl, lit);
  next = 0;
  for (;;) {
    tag = r0 & MASKCS;
    if (tag == BINCS || tag == TRNCS) {
      other = r0 >> RMSHFT;
      lgldstpull (lgl, other);
      if (tag == TRNCS) lgldstpull (lgl, r1);
    } else {
      assert (tag == LRGCS);
      for (p = lglidx2lits (lgl, (r0 & REDCS), r1); (other = *p); p++)
	if (other != lit) lgldstpull (lgl, *p);
    }
    if (next == lglcntstk (&lgl->seen)) break;
    lit = lglpeek (&lgl->seen, next++);
    av = lglavar (lgl, lit);
    assert ((lit < 0) == av->wasfalse);
    rsn = lglrsn (lgl, lit);
    r0 = rsn[0], r1 = rsn[1];
    LOGREASON (2, lit, r0, r1, "conflict distillation analysis of");
  }
  unit = (lglcntstk (&lgl->clause) == 1) ? lgl->clause.start[0] : 0;
  lglpopnunmarkstk (lgl, &lgl->seen);
#ifndef NLGLOG
  if (unit)
    LOG (1, "conflict distillilation analysis produced unit %d", unit);
  else LOG (2,
            "conflict distillilation analysis clause of size %d",
	    lglcntstk (&lgl->clause));
#endif
  lglpopnunmarkstk (lgl, &lgl->clause);
  return unit;
}

static int lgldistill (LGL * lgl) {
  int lidx, i, * clauses, lit, distilled, size, count, nlrg, ntrn, idx,sign;
  int * c, * p, * q, satisfied, res, newsize, antecedents, * start, * trn;
  int blit, tag, red, other, other2, ok, success;
  int64_t limit, oldprgss = lgl->stats.prgss;
  unsigned first, pos, delta, mod, last;
  int * w, * eow;
  HTS * hts;
  Val val;
  assert (lgl->opts.distill.val);
  assert (!lgl->distilling);
  assert (!lgl->simp);
  lglstart (lgl, &lgl->stats.tms.dst);
  lgl->distilling = 1;
  lgl->simp = 1;
  res = 1;
  lgl->stats.dst.count++;
  nlrg = 0;
  for (c = lgl->irr.start; c < lgl->irr.top; c = p) {
    p = c;
    lit = *p++;
    assert (lit);
    if (lit == REMOVED) continue;
    assert (p < lgl->irr.top);
    while (*p++) assert (p < lgl->irr.top);
    nlrg++;
  }
  if (nlrg) LOG (1, "distilling %d large clauses", nlrg);
  else LOG (1, "could not find any large irredundant clause to distill");
  ntrn = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = lglhts (lgl, lit);
      if (!hts->count) continue;
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	red = blit & REDCS;
	other = blit >> RMSHFT;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (tag != TRNCS) continue;
	if (red) continue;
	if (abs (other) < idx) continue;
	other2 = *p;
	if (abs (other2) < idx) continue;
	ntrn++;
      }
    }
  }
  if (ntrn) LOG (1, "distilling %d ternary clauses", ntrn);
  else LOG (1, "could not find any ternary irredundant clause to distill");
  mod = nlrg + ntrn;
  if (!mod) {
    LOG (1, "there are no irredundant clauses to distill");
    assert (res);
    goto NEXT;
  }
  NEW (trn, 3*ntrn*sizeof *trn);
  i = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = lglhts (lgl, lit);
      if (!hts->count) continue;
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	red = blit & REDCS;
	other = blit >> RMSHFT;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (tag != TRNCS) continue;
	if (red) continue;
	if (abs (other) < idx) continue;
	other2 = *p;
	if (abs (other2) < idx) continue;
	trn[i++] = lit;
	trn[i++] = other;
	trn[i++] = other2;
      }
    }
  }
  assert (i == 3*ntrn);
  lglchkbcpclean (lgl);
  if (lgl->level > 0) lglbacktrack (lgl, 0);
  assert (lgl->measureagility && lgl->propred);
  lgl->measureagility = lgl->propred = 0;
  assert (mod);
  pos = lglrand (lgl) % mod;
  delta = lglrand (lgl) % mod;
  if (!delta) delta++;
  while (lglgcd (delta, mod) > 1)
    if (++delta == mod) delta = 1;
  LOG (1, "distilling start %u delta %u mod %u", pos, delta, mod);
  if (lgl->stats.dst.count == 1) limit = lgl->opts.dstmaxeff.val/10;
  else limit = (lgl->opts.dstreleff.val*lgl->stats.visits.search)/1000;
  if (limit < lgl->opts.dstmineff.val) limit = lgl->opts.dstmineff.val;
  if (limit > lgl->opts.dstmaxeff.val) limit = lgl->opts.dstmaxeff.val;
  LOG (2, "distilling with penalty %d", lgl->limits.dst.pen);
  if (lgl->limits.dst.pen < 0) limit <<= -lgl->limits.dst.pen;
  if (lgl->limits.dst.pen > 0) limit >>= lgl->limits.dst.pen;
  LOG (2, "distilling with up to %lld propagations", limit);
  limit += lgl->stats.visits.simp;
  NEW (clauses, mod);
  i = 0;
  start = lgl->irr.start;
  for (c = start; c < lgl->irr.top; c = p) {
    p = c;
    lit = *p++;
    assert (lit);
    if (lit == REMOVED) continue;
    assert (p < lgl->irr.top);
    while (*p++) assert (p < lgl->irr.top);
    assert (i < mod);
    clauses[i++] = c - start;
  }
  first = mod;
  success = count = distilled = 0;
  assert (i == nlrg);
  while (lgl->stats.visits.simp < limit && !lglterminate (lgl)) {
    assert (res);
    if (!(res = lglsyncunits (lgl))) { assert (lgl->mt); goto DONE; }
    lglchkbcpclean (lgl);
    count++;
    assert (count <= mod);
    if (pos < nlrg) {
      lidx = clauses[pos];
      c = start + lidx;
      if (*c == REMOVED) goto CONTINUE;
      LOGCLS (2, c, "distilling large %d clause", lidx);
      satisfied = (lglval (lgl, c[0]) > 0 || lglval (lgl, c[1]) > 0);
      q = c + 2;
      for (p = q; (lit = *p); p++) {
	if (satisfied) continue;
	val = lglval (lgl, lit);
	if (val < 0) continue;
	if (val > 0) { satisfied = lit; continue; }
	*q++ = lit;
      }
      if (!satisfied) assert (!lglval (lgl, c[0]) && !lglval (lgl, c[1]));
      size = q - c;
      *q++ = 0;
      while (q <= p) *q++ = REMOVED;
      if (satisfied || size <= 3) {
	lglrmlwch (lgl, c[0], 0, lidx);
	lglrmlwch (lgl, c[1], 0, lidx);
      }
      if (satisfied) {
	LOGCLS (2, c, "distilled large %d clause already %d satisfied",
		lidx, satisfied);
      } else if (size == 2) {
	LOG (2, "found new binary clause distilling large %d clause", lidx);
	lglwchbin (lgl, c[0], c[1], 0);
	lglwchbin (lgl, c[1], c[0], 0);
      } else if (size == 3) {
	LOG (2, "found new ternary clause distilling large %d clause", lidx);
	lglwchtrn (lgl, c[0], c[1], c[2], 0);
	lglwchtrn (lgl, c[1], c[0], c[2], 0);
	lglwchtrn (lgl, c[2], c[0], c[1], 0);
      } else assert (size > 3);
      if (satisfied) lgldeclscnt (lgl, size, 0, 0);
      if (satisfied || size <= 3) {
	while (p >= c) *p-- = REMOVED;
	goto CONTINUE;
      }
      distilled++;
      assert (lgl->ignlidx < 0);
      lgl->ignlidx = lidx;
      ok = 1;
      val = 0;
      for (p = c; (lit = *p); p++) {
	val = lglval (lgl, lit);
	if (val) break;
	lgliassume (lgl, -lit);
	ok = lglbcp (lgl);
	if (!ok) break;
      }
      lgl->ignlidx = -1;
#ifndef NDEBUG
      if (lit) assert (!val != !lgl->conf.lit);
      else assert (!val && !lgl->conf.lit);
#endif
      if (ok || !lit) lglbacktrack (lgl, 0);
      if (!lit) goto CONTINUE;
      lglrmlwch (lgl, c[0], 0, lidx);
      lglrmlwch (lgl, c[1], 0, lidx);
      if (val < 0) {
	assert (ok);
	assert (size >= 4);
	lgl->stats.dst.str++;
	lgl->stats.prgss++;
	success++;
	LOGCLS (2, c,
		"removing literal %d in distilled large %d clause",
		lit, lidx);
	for (p = c; (*p != lit); p++)
	  ;
	for (q = p++; (lit = *p); p++)
	  *q++ = lit;
	*q++ = 0;
	*q = REMOVED;
	if (size == 4) goto LRG2TRN; else goto LRG2LRG;
      } else if (val > 0) {
	assert (ok);
	newsize = p - c + 1;
	assert (2 <= newsize && newsize <= size);
	if (newsize == size) goto LRGRED;
	antecedents = lgldstanalit (lgl, lit);
	if (antecedents > 1) {
	  p = q = c;
	  while (q < c + newsize) {
	    lit = *q++;
	    if (lglmarked (lgl, lit)) *p++ = lit;
	  }
	  p--;
	  assert (p - c + 1 <= newsize);
	  newsize = p - c + 1;
	  assert (2 <= newsize && newsize <= size);
	}
	lglpopnunmarkstk (lgl, &lgl->clause);
	if (antecedents == 1) goto LRGRED;
	lgl->stats.dst.str++;
	lgl->stats.prgss++;
	LOGCLS (2, c, "shortening distilled large %d clause by %d literals",
		lidx, size - newsize);
	*++p = 0;
	while (*++p) *p = REMOVED;
	*p = REMOVED;
	if (newsize == 2) {
//LRG2BIN:
	  LOG (2, "distilled large %d clause becomes binary clause %d %d",
	       lidx, c[0], c[1]);
#ifndef NLGLPICOSAT
	  lglpicosatchkclsarg (lgl, c[0], c[1], 0);
#endif
	  lglwchbin (lgl, c[0], c[1], 0);
	  lglwchbin (lgl, c[1], c[0], 0);
	  c[0] = c[1] = c[2] = REMOVED;
	  assert (c[3] == REMOVED);
	} else if (newsize == 3) {
LRG2TRN:
	  LOG (2,
	       "distilled large %d clause becomes ternary clause %d %d %d",
	       lidx, c[0], c[1], c[2]);
#ifndef NLGLPICOSAT
	  lglpicosatchkclsarg (lgl, c[0], c[1], c[2], 0);
#endif
	  lglwchtrn (lgl, c[0], c[1], c[2], 0);
	  lglwchtrn (lgl, c[1], c[0], c[2], 0);
	  lglwchtrn (lgl, c[2], c[0], c[1], 0);
	  c[0] = c[1] = c[2] = c[3] = REMOVED;
	  assert (c[4] == REMOVED);
	} else {
LRG2LRG:
	  (void) lglwchlrg (lgl, c[1], c[0], 0, lidx);
	  (void) lglwchlrg (lgl, c[0], c[1], 0, lidx);
	  LOGCLS (2, c, "distilled %d clause remains large clause", lidx);
#ifndef NLGLPICOSAT
	  lglpicosatchkclsaux (lgl, c);
#endif
	}
      } else if (p == c) {
	assert (!ok);
	assert (lgl->conf.lit);
	lit = lgldstanaconf (lgl);
	assert (lit);
	lglbacktrack (lgl, 0);
LRGFAILED:
	lgl->stats.dst.failed++;
	lgl->stats.prgss++;
	LOG (1, "failed literal %d during distilling large %d clause",
	     -lit, lidx);
	lglunit (lgl, lit);
	assert (!lgl->level);
	assert (!lgl->propred);
	lgl->propred = 1;
	res = lglbcp (lgl);
	lgl->propred = 0;
	if (!res) { assert (!lgl->mt); lgl->mt = 1; goto DONE; }
	goto LRGREM;
      } else {
	assert (!ok);
	assert (lgl->conf.lit);
	lit = lgldstanaconf (lgl);
	lglbacktrack (lgl, 0);
	if (lit) goto LRGFAILED;
LRGRED:
	LOGCLS (2, c, "redundant distilled large %d clause", lidx);
	lgl->stats.dst.red++;
	lgl->stats.prgss++;
LRGREM:
	for (p = c; *p; p++) *p = REMOVED;
	*p = REMOVED;
	lgldeclscnt (lgl, size, 0, 0);
      }
    } else {
      lidx = pos - nlrg;
      assert (0 <= lidx && lidx < ntrn);
      c = trn + 3*lidx;
      if (*c == REMOVED) goto CONTINUE;
      LOG (2, "distilling ternary clause %d %d %d", c[0], c[1], c[2]);
      for (i = 0; i < 3; i++) {
	if (lglval (lgl, c[i]) <= 0) continue;
	LOG (2, "distilled ternary clause %d %d %d already satisfied by %d",
	     c[0], c[1], c[2], c[i]);
	goto TRNREM;
      }
      for (i = 0; i < 3; i++) {
	val = lglval (lgl, c[i]);
	if (!val) continue;
	assert (val < 0);
	if (i != 2) SWAP (c[i], c[2]);
	LOG (2, "removing false %d from distilled ternary clause %d %d %d",
	     c[i], c[0], c[1], c[2]);
	goto TRN2BIN;
      }
      distilled++;
      assert (!lgl->igntrn);
      for (i = 0; i < 3; i++) lgl->ignlits[i] = c[i];
      lgl->igntrn = 1;
      ok = 1;
      val = 0;
      lit = 0;
      for (i = 0; i < 3; i++) {
	lit = c[i];
	val = lglval (lgl, lit);
	if (val) break;
	lgliassume (lgl, -lit);
	ok = lglbcp (lgl);
	if (!ok) break;
      }
#ifndef NDEBUG
      if (i < 3) assert (!val != !lgl->conf.lit);
      else assert (!val && !lgl->conf.lit);
#endif
      if (val || i == 3) lglbacktrack (lgl, 0);
      assert (lgl->igntrn);
      lgl->igntrn = 0;
      if (i == 3) goto CONTINUE;
      if (val < 0) {
	assert (ok);
	assert (i >= 1);
	lgl->stats.dst.str++;
	lgl->stats.prgss++;
	if (i != 2) SWAP (c[i], c[2]);
TRN2BIN:
	assert (!lglval (lgl, c[0]));
	assert (!lglval (lgl, c[1]));
	LOG (2, "distilled ternary clause becomes binary clause %d %d",
	     c[0], c[1]);
#ifndef NLGLPICOSAT
	lglpicosatchkclsarg (lgl, c[0], c[1], 0);
#endif
	lgl->stats.irr++; assert (lgl->stats.irr > 0);
	lglwchbin (lgl, c[0], c[1], 0);
	lglwchbin (lgl, c[1], c[0], 0);
	goto TRNREM;
      } else if (val > 0) {
	assert (i > 0);
	if (i == 2) goto TRNRED;
	assert (i == 1);
	antecedents = lgldstanalit (lgl, lit);
	lglpopnunmarkstk (lgl, &lgl->clause);
	if (antecedents == 1) goto TRNRED;
	lgl->stats.dst.str++;
	lgl->stats.prgss++;
	goto TRN2BIN;
      } else if (i == 0) {
	assert (!ok);
	assert (lgl->conf.lit);
	lit = lgldstanaconf (lgl);
	assert (lit);
	lglbacktrack (lgl, 0);
TRNFAILED:
        lgl->stats.dst.failed++;
	lgl->stats.prgss++;
	LOG (1, "failed literal %d during distilling ternary clause", -lit);
	lglunit (lgl, lit);
	assert (!lgl->level);
	assert (!lgl->propred);
	lgl->propred = 1;
	res = lglbcp (lgl);
	lgl->propred = 0;
	if (!res) { assert (!lgl->mt); lgl->mt = 1; goto DONE; }
	else goto TRNREM;
      } else {
	assert (!ok);
	assert (lgl->conf.lit);
	lit = lgldstanaconf (lgl);
	lglbacktrack (lgl, 0);
	if (lit) goto TRNFAILED;
TRNRED:
	LOG (2,
	     "redundant distilled ternary clause %d %d %d",
	     c[0], c[1], c[2]);
	lgl->stats.dst.red++;
	lgl->stats.prgss++;
TRNREM:
	lglrmtwch (lgl, c[0], c[1], c[2], 0);
	lglrmtwch (lgl, c[1], c[0], c[2], 0);
	lglrmtwch (lgl, c[2], c[0], c[1], 0);
	lgldeclscnt (lgl, 3, 0, 0);
	*c = REMOVED;
      }
    }
CONTINUE:
    last = pos;
    pos += delta;
    if (pos >= mod) pos -= mod;
    if (pos == first) { assert (count == mod); break; }
    if (mod == 1) break;
    if (first == mod) first = last;
  }
DONE:
  assert (res || lgl->mt);
  DEL (trn, 3*ntrn*sizeof *trn);
  DEL (clauses, mod);
  lglfitstk (lgl, &lgl->irr);
  assert (!lgl->measureagility && !lgl->propred);
  lgl->measureagility = lgl->propred = 1;
  success = oldprgss < lgl->stats.prgss;
  if (success && lgl->limits.dst.pen > MINPEN) lgl->limits.dst.pen--;
  if (!success && lgl->limits.dst.pen < MAXPEN) lgl->limits.dst.pen++;
  LOG (1,
       "%ssuccessfully distilled %d clauses",
       success ? "" : "un", distilled);
  lglrep (lgl, 1, 'l');
NEXT:
  lgl->limits.dst.vinc += lgl->opts.dstvintinc.val;
  lgl->limits.dst.cinc += lgl->opts.dstcintinc.val;
  lgl->limits.dst.visits = lgl->stats.visits.search + lgl->limits.dst.vinc;
  lgl->limits.dst.confs = lgl->stats.confs + lgl->limits.dst.cinc;
  lgl->limits.dst.irr = lgl->stats.irr + lgl->opts.dstirrintinc.val;
  lgl->limits.dst.prgss = lgl->stats.prgss;
  assert (lgl->simp);
  assert (lgl->distilling);
  lgl->distilling = 0;
  lgl->simp = 0;
  lglstop (lgl);
  return res;
}

static int lgltrdbin (LGL * lgl, int start, int target, int irr) {
  int lit, next, blit, tag, red, other, * p, * w, * eow, res, ign, val;
  HTS * hts;
  assert (lglmtstk (&lgl->seen));
  assert (abs (start) < abs (target));
  LOG (2, "trying transitive reduction of %s binary clause %d %d",
       lglred2str (irr^REDCS), start, target);
  lgl->stats.trd.bins++;
  lglpushnmarkseen (lgl, -start);
  next = 0;
  res = 0;
  ign = 1;
  while (next < lglcntstk (&lgl->seen)) {
    lit = lglpeek (&lgl->seen, next++);
    lgl->stats.trd.steps++;
    LOG (3, "transitive reduction search step %d", lit);
    val = lglval (lgl, lit);
    if (val) continue;
    hts = lglhts (lgl, -lit);
    if (!hts->count) continue;
    w = lglhts2wchs (lgl, hts);
    eow = w + hts->count;
    for (p = w; p < eow; p++) {
      blit = *p;
      tag = blit & MASKCS;
      if (tag == LRGCS || tag == TRNCS) p++;
      if (tag != BINCS) continue;
      red = blit & REDCS;
      if (irr && red) continue;
      other = blit >> RMSHFT;
      if (other == start) continue;
      if (other == target) {
	if (lit == -start && ign) { ign = 0; continue; }
	LOG (2, "transitive path closed with %s binary clause %d %d",
	     lglred2str (red), -lit, other);
	res = 1;
	goto DONE;
      }
      val = lglmarked (lgl, other);
      if (val > 0) continue;
      if (val < 0) {
	assert (lgl->level == 0);
	lgl->stats.trd.failed++;
        LOG (1, "failed literal %d in transitive reduction", -start);
	lglunit (lgl, start);
	val = lglbcp (lgl);
	if (!val && !lgl->mt) lgl->mt = 1;
	assert (val || lgl->mt);
	res = -1;
	goto DONE;
      }
      lglpushnmarkseen (lgl, other);
      LOG (3, "transitive reduction follows %s binary clause %d %d",
           lglred2str (red), -lit, other);
    }
  }
DONE:
  lglpopnunmarkstk (lgl, &lgl->seen);
  return res;
}

static void lgltrdlit (LGL * lgl, int start) {
  int target, * w, * p, * eow, blit, tag, red, val;
#ifndef NDEBUG
  int unassigned = lgl->unassigned;
#endif
  HTS * hts;
  val = lglval (lgl, start);
  if (val) return;
  LOG (2, "transitive reduction of binary clauses with %d", start);
  assert (lglmtstk (&lgl->seen));
  hts = lglhts (lgl, start);
  if (!hts->count) return;
  lgl->stats.trd.lits++;
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  for (p = w;
       p < eow && (lgl->stats.trd.steps < lgl->limits.trd.steps);
       p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag != BINCS) continue;
    target = blit >> RMSHFT;
    if (abs (start) > abs (target)) continue;
    red = blit & REDCS;
    val = lgltrdbin (lgl, start, target, red^REDCS);
    if (!val) continue;
    if (val < 0) { assert (lgl->mt || lgl->unassigned < unassigned); break; }
    LOG (2, "removing transitive redundant %s binary clause %d %d",
         lglred2str (red), start, target);
    lgl->stats.trd.red++;
    lgl->stats.prgss++;
    lglrmbwch (lgl, start, target, red);
    lglrmbwch (lgl, target, start, red);
    assert (!lgl->dense);
    if (red) break;
    assert (lgl->stats.irr > 0);
    lgl->stats.irr--;
    break;
  }
}

static int lgltrd (LGL * lgl) {
  unsigned pos, delta, mod, ulit, first, last;
  int64_t limit, oldprgss = lgl->stats.prgss;;
  int lit, count, success;
  if (lgl->nvars <= 2) return 1;
  lgl->stats.trd.count++;
  lglstart (lgl, &lgl->stats.tms.trd);
  if (lgl->level > 0) lglbacktrack (lgl, 0);
  mod = 2*(lgl->nvars - 2);
  assert (mod > 0);
  pos = lglrand (lgl) % mod;
  delta = lglrand (lgl) % mod;
  if (!delta) delta++;
  while (lglgcd (delta, mod) > 1)
    if (++delta == mod) delta = 1;
  LOG (1, "transitive reduction start %u delta %u mod %u", pos, delta, mod);
  if (lgl->stats.trd.count == 1) limit = lgl->opts.trdmaxeff.val/10;
  else limit = (lgl->opts.trdreleff.val*lgl->stats.visits.search)/1000;
  if (limit < lgl->opts.trdmineff.val) limit = lgl->opts.trdmineff.val;
  if (limit > lgl->opts.trdmaxeff.val) limit = lgl->opts.trdmaxeff.val;
  LOG (2, "transitive reduction penalty %d", lgl->limits.trd.pen);
  if (lgl->limits.trd.pen < 0) limit <<= -lgl->limits.trd.pen;
  if (lgl->limits.trd.pen > 0) limit >>= lgl->limits.trd.pen;
  LOG (2, "transitive reduction with up to %lld search steps", limit);
  lgl->limits.trd.steps = lgl->stats.trd.steps + limit;
  first = mod;
  count = 0;
  while (lgl->stats.trd.steps < lgl->limits.trd.steps) {
    if (lglterminate (lgl)) break;
    if (!lglsyncunits (lgl)) break;
    ulit = pos + 4;
    lit = lglilit (ulit);
    lgltrdlit (lgl, lit);
    count++;
    assert (count <= mod);
    if (lgl->mt) break;
    last = pos;
    pos += delta;
    if (pos >= mod) pos -= mod;
    if (pos == first) { assert (count == mod); break; }
    if (mod == 1) break;
    if (first == mod) first = last;
  }
  success = oldprgss < lgl->stats.prgss;
  if (success && lgl->limits.trd.pen > MINPEN) lgl->limits.trd.pen--;
  if (!success && lgl->limits.trd.pen < MAXPEN) lgl->limits.trd.pen++;
  lglrep (lgl, 1, 't');
  lglstop (lgl);
  lgl->limits.trd.cinc += lgl->opts.trdcintinc.val;
  lgl->limits.trd.vinc += lgl->opts.trdvintinc.val;
  lgl->limits.trd.visits = lgl->stats.visits.search + lgl->limits.trd.vinc;
  lgl->limits.trd.confs = lgl->stats.confs + lgl->limits.trd.cinc;
  lgl->limits.trd.irr = lgl->stats.irr + lgl->opts.trdirrintinc.val;
  lgl->limits.trd.prgss = lgl->stats.prgss;
  return !lgl->mt;
}

static int lglunhdhasbins (LGL * lgl, const DFPR * dfpr,
                           int lit, int irronly) {
  int blit, tag, other, val, red, ulit;
  const int * p, * w, * eos;
  HTS * hts;
  assert (!lglval (lgl, lit));
  hts = lglhts (lgl, lit);
  w = lglhts2wchs (lgl, hts);
  eos = w + hts->count;
  for (p = w; p < eos; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == IRRCS) continue;
    if (tag == TRNCS || tag == LRGCS) { p++; continue; }
    red = blit & REDCS;
    if (irronly && red) continue;
    other = blit >> RMSHFT;
    val = lglval (lgl, other);
    assert (val >= 0);
    if (val > 0) continue;
    ulit = lglulit (other);
    if (!dfpr[ulit].discovered) return 1;
  }
  return 0;
}

static int lglunhdisroot (LGL * lgl, int lit, DFPR * dfpr, int irronly) {
  int res = !lglunhdhasbins (lgl, dfpr, lit, irronly);
  assert (!res || !dfpr[lglulit (lit)].discovered);
  return res;
}

static int lglmtwtk (Wtk * wtk) { return wtk->top == wtk->start; }

static int lglfullwtk (Wtk * wtk) { return wtk->top == wtk->end; }

static int lglsizewtk (Wtk * wtk) { return wtk->end - wtk->start; }

static int lglcntwtk (Wtk * wtk) { return wtk->top - wtk->start; }

static void lglrelwtk (LGL * lgl, Wtk * wtk) {
  DEL (wtk->start, lglsizewtk (wtk));
  memset (wtk, 0, sizeof *wtk);
}

static void lglenlwtk (LGL * lgl, Wtk * wtk) {
  int oldsize = lglsizewtk (wtk);
  int newsize = oldsize ? 2*oldsize : 1;
  int count = lglcntwtk (wtk);
  RSZ (wtk->start, oldsize, newsize);
  wtk->top = wtk->start + count;
  wtk->end = wtk->start + newsize;
}

static void lglpushwtk (LGL * lgl, Wtk * wtk,
                        Wrag wrag, int lit, int other, int red) {
  Work w;
  if (lglfullwtk (wtk)) lglenlwtk (lgl, wtk);
  w.wrag = wrag;
  w.other = other;
  w.red = red ? 1 : 0;
  w.removed = 0;
  w.lit = lit;
  *wtk->top++ = w;
}

#define lglpopwtk(WTK,WRAG,LIT,OTHER,RED,REMOVED) \
do { \
  assert (!lglmtwtk (WTK)); \
  (WTK)->top--; \
  (WRAG) = (WTK)->top->wrag; \
  (LIT) = (WTK)->top->lit; \
  (OTHER) = (WTK)->top->other; \
  (RED) = (WTK)->top->red ? REDCS : 0; \
  (REMOVED) = (WTK)->top->removed; \
} while (0)

static int lglstamp (LGL * lgl, int root,
                     DFPR * dfpr, DFOPF * dfopf,
		     Wtk * work, Stk * units, Stk * sccs, Stk * trds,
		     int * visitedptr, int stamp, int irronly) {
  int uroot, lit, ulit, blit, tag, red, other, failed, uother, unotother;
  int observed, discovered, pos, undiscovered;
  unsigned start, end, mod, i, j, sccsize;
  const int * p, * w, * eos;
  int startstamp;
  const Work * r;
  int removed;
  HTS * hts;
  Wrag wrag;
  if (lglval (lgl, root)) return stamp;
  uroot =  lglulit (root);
  if (dfpr[uroot].discovered) return stamp;
  assert (!dfpr[uroot].finished);
  assert (lglmtwtk (work));
  assert (lglmtstk (units));
  assert (lglmtstk (sccs));
  assert (lglmtstk (trds));
  LOG (3, "stamping dfs %s %d %s",
       (lglunhdisroot (lgl, root, dfpr, irronly) ? "root" : "start"), root,
       irronly ? "only over irredundant clauses" :
                 "also over redundant clauses");
  startstamp = 0;
  lglpushwtk (lgl, work, PREFIX, root, 0, 0);
  while (!lglmtwtk (work)) {
    lgl->stats.unhd.steps++;
    lglpopwtk (work, wrag, lit, other, red, removed);
    if (removed) continue;
    if (wrag == PREFIX) {
      ulit = lglulit (lit);
      if (dfpr[ulit].discovered) {
	dfopf[ulit].observed = stamp;
	LOG (3, "stamping %d observed %d", lit, stamp);
	continue;
      }
      assert (!dfpr[ulit].finished);
      dfpr[ulit].discovered = ++stamp;
      dfopf[ulit].observed = stamp;
      LOG (3, "stamping %d observed %d", lit, stamp);
      *visitedptr += 1;
      if (!startstamp) {
	startstamp = stamp;
	LOG (3, "root %d with stamp %d", lit, startstamp);
	dfpr[ulit].root = lit;
	LOG (4, "stamping %d root %d", lit, lit);
	assert (!dfpr[ulit].parent);
	LOG (4, "stamping %d parent %d", lit, 0);
      }
      LOG (4, "stamping %d discovered %d", lit, stamp);
      lglpushwtk (lgl, work, POSTFIX, lit, 0, 0);
      assert (dfopf[ulit].pushed < 0);
      dfopf[ulit].pushed = lglcntwtk (work);
      assert (!dfopf[ulit].flag);
      dfopf[ulit].flag = 1;
      lglpushstk (lgl, sccs, lit);
      hts = lglhts (lgl, -lit);
      w = lglhts2wchs (lgl, hts);
      eos = w + hts->count;
      for (undiscovered = 0; undiscovered <= 1 ; undiscovered++) {
	start = lglcntwtk (work);
	for (p = w; p < eos; p++) {
	  blit = *p;
	  tag = blit & MASKCS;
	  if (tag == IRRCS) continue;
	  if (tag == TRNCS || tag == LRGCS) { p++; continue; }
	  assert (tag == BINCS);
	  red = blit & REDCS;
	  if (irronly && red) continue;
	  other = blit >> RMSHFT;
	  if (lglval (lgl, other)) continue;
	  uother = lglulit (other);
	  if (undiscovered != !dfpr[ulit].discovered) continue;
	  // kind of defensive, since 'lglrmbindup' should avoid it
	  // and this fix may not really work anyhow since it does
	  // not distinguish between irredundant and redundant clauses
	  COVER (lglsignedmarked (lgl, other) > 0);
	  if (lglsignedmarked (lgl, other) > 0) {
	    LOG (2, "stamping skips duplicated edge %d %d", lit, other);
	    continue;
	  }
	  lglsignedmark (lgl, other);
	  lglpushwtk (lgl, work, BEFORE, lit, other, red);
	}
	end = lglcntwtk (work);
	for (r = work->start + start; r < work->top; r++) 
	  lglunmark (lgl, r->other);
	mod = (end - start);
	if (mod <= 1) continue;
	for (i = start; i < end - 1;  i++) {
	  assert (1 < mod && mod == (end - i));
	  j = lglrand (lgl) % mod--;
	  if (!j) continue;
	  j = i + j;
	  SWAP (work->start[i], work->start[j]);
	}
      }
    } else if (wrag == BEFORE) {	// before recursive call
      LOG (2, "stamping edge %d %d before recursion", lit, other);
      lglpushwtk (lgl, work, AFTER, lit, other, red);
      ulit = lglulit (lit);
      uother = lglulit (other);
      unotother = lglulit (-other);
      if (lgl->opts.unhdextstamp.val && (irronly || red) &&
	  dfopf[uother].observed > dfpr[ulit].discovered) {
	LOG (2, "transitive edge %d %d during stamping", lit, other);
	lgl->stats.unhd.stamp.trds++;
	lgl->stats.prgss++;
	if (red) lgl->stats.unhd.tauts.red++;
	lglrmbcls (lgl, -lit, other, red);
	if ((pos = dfopf[unotother].pushed) >= 0) {
	  while (pos  < lglcntwtk (work)) {
	    if (work->start[pos].lit != -other) break;
	    if (work->start[pos].other == -lit) {
	      LOG (3, "removing edge %d %d from DFS stack", -other, -lit);
	      work->start[pos].removed = 1;
	    }
	    pos++;
	  }
	}
	work->top--;
	assert (dfpr[uother].discovered); // and thus 'parent' + 'root' set
	continue;
      }
      observed = dfopf[unotother].observed;
      if (lgl->opts.unhdextstamp.val && startstamp <= observed) {
	LOG (1, "stamping failing edge %d %d", lit, other);
	for (failed = lit;
	     dfpr[lglulit (failed)].discovered > observed;
	     failed = dfpr[lglulit (failed)].parent)
	  assert (failed);
	LOG (1, "stamping failed literal %d", failed);
	lglpushstk (lgl, units, -failed);
	lgl->stats.unhd.stamp.failed++;
	if (dfpr[unotother].discovered && !dfpr[unotother].finished) {
	  LOG (2, "stamping skips edge %d %d after failed literal %d",
	       lit, other, failed);
	  work->top--;
	  continue;
	}
      }
      if (!dfpr[uother].discovered) {
	dfpr[uother].parent = lit;
	LOG (4, "stamping %d parent %d", other, lit);
	dfpr[uother].root = root;
	LOG (4, "stamping %d root %d", other, root);
	lglpushwtk (lgl, work, PREFIX, other, 0, 0);
      }
    } else if (wrag == AFTER) {		// after recursive call
      LOG (2, "stamping edge %d %d after recursion", lit, other);
      uother = lglulit (other);
      ulit = lglulit (lit);
      if (lgl->opts.unhdextstamp.val && !dfpr[uother].finished &&
          dfpr[uother].discovered < dfpr[ulit].discovered) {
	LOG (2, "stamping back edge %d %d", lit, other);
	dfpr[ulit].discovered = dfpr[uother].discovered;
        LOG (3, "stamping %d reduced discovered to %d",
	     lit, dfpr[ulit].discovered);
	if (dfopf[ulit].flag) {
	  LOG (2, "stamping %d as being part of a non-trivial SCC", lit);
	  dfopf[ulit].flag = 0;
	}
      }
      dfopf[uother].observed = stamp;
      LOG (3, "stamping %d observed %d", other, stamp);
    } else {
      assert (wrag == POSTFIX);
      LOG (2, "stamping postfix %d", lit);
      ulit = lglulit (lit);
      if (dfopf[ulit].flag) {
	stamp++;
	sccsize = 0;
	discovered = dfpr[ulit].discovered;
	do {
	  other = lglpopstk (sccs);
	  uother = lglulit (other);
	  dfopf[uother].pushed = -1;
	  dfopf[uother].flag = 0;
	  dfpr[uother].discovered = discovered;
	  dfpr[uother].finished = stamp;
	  LOG (3, "stamping %d interval %d %d parent %d root %d",
	       other, dfpr[uother].discovered, dfpr[uother].finished,
	       dfpr[uother].parent, dfpr[uother].root);
	  sccsize++;
	} while (other != lit);
        assert (lgl->opts.unhdextstamp.val || sccsize == 1);
	if (sccsize > 1) {
	  LOG (2, "stamping non trivial SCC of size %d", sccsize);
	  lgl->stats.unhd.stamp.sumsccsizes += sccsize;
	  lgl->stats.unhd.stamp.sccs++;
	}
      } else assert (lgl->opts.unhdextstamp.val);
    }
  }
  assert (lglmtwtk (work));
  assert (lglmtstk (sccs));
  return stamp;
}

static int lglunhlca (LGL * lgl, const DFPR * dfpr, int a, int b) {
  const DFPR * c, * d;
  int u, v, p;
  if (a == b) return a;
  u = lglulit (a), v = lglulit (b);
  c = dfpr + u, d = dfpr + v;
  if (c->discovered <= d->discovered) {
    p = a;
  } else {
    assert (c->discovered > d->discovered);
    p = b;
    SWAP (c, d);
  }
  for (;;) {
    assert (c->discovered <= d->discovered);
    if (d->finished <= c->finished) break;
    p = c->parent;
    if (!p) break;
    u = lglulit (p);
    c = dfpr + u;
  }
  LOG (3, "unhiding least common ancestor of %d and %d is %d", a, b, p);
  return p;
}

static int lglunhidefailed (LGL * lgl, const DFPR * dfpr) {
  int idx, sign, lit, unit, nfailed = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    for (sign = -1; sign <= 1; sign += 2) {
      if (lglterminate (lgl)) return 0;
      if (!lglsyncunits (lgl)) return 0;
      lgl->stats.unhd.steps++;
      lit = sign * idx;
      if (lglval (lgl, lit)) continue;
      if (!dfpr[lglulit (lit)].discovered) continue;
      if (lglunhimplincl (dfpr, lit, -lit)) {
	unit = -lit;
	LOG (2, "unhiding %d implies %d", lit, -lit);
      } else if (lglunhimplincl (dfpr, -lit, lit)) {
	unit = lit;
	LOG (2, "unhiding %d implies %d", -lit, lit);
      } else continue;
      LOG (1, "unhiding failed literal %d", -unit);
      lglunit (lgl, unit);
      lgl->stats.unhd.failed.lits++;
      nfailed++;
      if (lglbcp (lgl)) continue;
      LOG (1, "empty clause after propagating unhidden failed literal");
      assert (!lgl->mt);
      lgl->mt = 1;
      return 0;
    }
  }
  LOG (1, "unhiding %d failed literals in this round", nfailed);
  return 1;
}

static int lglunhroot (const DFPR * dfpr, int lit) {
  return dfpr[lglulit (lit)].root;
}

static int lglunhidebintrn (LGL * lgl, const DFPR * dfpr, int irronly) {
  int idx, sign, lit, blit, tag, red, other, other2, unit, root, lca;
  int nbinred, ntrnred, nbinunits, ntrnunits, ntrnstr, ntrnhbrs;
  const int * p, * eow;
  int ulit, uother;
  int * w , * q;
  long delta;
  HTS * hts;
  nbinred = ntrnred = nbinunits = ntrnunits = ntrnstr = ntrnhbrs = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    for (sign = -1; sign <= 1; sign += 2) {
      if (lglterminate (lgl)) return 0;
      if (!lglsyncunits (lgl)) return 0;
      lgl->stats.unhd.steps++;
      lit = sign * idx;
      if (lglval (lgl, lit)) continue;
      ulit = lglulit (lit);
      if (!dfpr[ulit].discovered) continue;
      hts = lglhts (lgl, lit);
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      q = w;
      for (p = w; p < eow; p++) {
	blit = *p;
	*q++ = blit;
	tag = blit & MASKCS;
	if (tag == TRNCS || tag == LRGCS) *q++ = *++p;
	if (tag == LRGCS) continue;
	red = blit & REDCS;
	other = blit >> RMSHFT;
	if (lglval (lgl, other)) continue;
	uother = lglulit (other);
	if (tag == BINCS) {
	  if (lglunhimplies2 (dfpr, other, lit)) {
	    LOG (2, "unhiding removal of literal %d "
	            "with implication %d %d from binary clause %d %d",
	         other, other, lit, lit, other);
	    lgl->stats.unhd.units.bin++;
	    nbinunits++;
            unit = lit;
UNIT:
	    lglunit (lgl, unit);
	    p++;
	    while (p < eow) *q++ = *p++;
	    lglshrinkhts (lgl, hts, hts->count - (p - q));
	    if (lglbcp (lgl)) goto NEXTIDX;
	    LOG (1, "empty clause after propagating unhidden lifted unit");
	    assert (!lgl->mt);
	    lgl->mt = 1;
	    return 0;
	  } else if ((root = lglunhroot (dfpr, -lit)) &&
	             !lglval (lgl, root) &&
	             root == lglunhroot (dfpr, -other)) {
	    LOG (2, "negated literals in binary clause %d %d implied by %d",
	         lit, other, root);
	    lgl->stats.unhd.failed.bin++;
	    lca = lglunhlca (lgl, dfpr, -lit, -other);
	    unit = -lca;
	    assert (unit);
	    goto UNIT;
	  } else if (!irronly && !red) continue;
	  else {
	    if (dfpr[uother].parent == -lit) continue;
	    if (dfpr[ulit].parent == -other) continue;
	    if (!lglunhimplies2 (dfpr, -lit, other)) continue;
	    LOG (2, "unhiding tautological binary clause %d %d", lit, other);
	    lgl->stats.unhd.tauts.bin++;
	    lgl->stats.prgss++;
	    if (red) lgl->stats.unhd.tauts.red++;
	    nbinred++;
	    lglrmbwch (lgl, other, lit, red);
	    LOG (2, "removed %s binary clause %d %d",
		 lglred2str (red), lit, other);
	    lgldeclscnt (lgl, 2, red, 0);
	    assert (!lgl->dense);
	    q--;
	  }
	} else {
	  assert (tag == TRNCS);
	  other2 = *p;
	  if (lglval (lgl, other2)) continue;
	  if (lglunhimplies2incl (dfpr, other, lit) &&
	      lglunhimplies2incl (dfpr, other2, lit)) {
	    LOG (2,
	         "unhiding removal of literals %d and %d with implications "
		 "%d %d and %d %d from ternary clause %d %d %d",
		 other, other2,
		 other, lit,
		 other2, lit,
		 lit, other, other2);
	    lgl->stats.unhd.str.trn += 2;
	    if (red) lgl->stats.unhd.str.red += 2;
	    lgl->stats.unhd.units.trn++;
	    ntrnunits++;
	    unit = lit;
	    goto UNIT;
	  } else if ((root = lglunhroot (dfpr, -lit)) &&
	             !lglval (lgl, root) &&
	             root == lglunhroot (dfpr, -other) &&
	             root == lglunhroot (dfpr, -other2)) {
	    LOG (2,
	      "negation of literals in ternary clauses %d %d %d "
	      "implied by %d", lit, other, other2, root);
	    lgl->stats.unhd.failed.trn++;
	    lca = lglunhlca (lgl, dfpr, -lit, -other);
	    assert (lca);
	    lca = lglunhlca (lgl, dfpr, lca, -other2);
	    assert (lca);
	    unit = -lca;
	    goto UNIT;
	  } else if ((red || irronly) &&
	             (lglunhimplies2incl (dfpr, -lit, other) ||
	              lglunhimplies2incl (dfpr, -lit, other2))) {
	    LOG (2, "unhiding tautological ternary clause %d %d %d",
		 lit, other, other2);
	    lgl->stats.unhd.tauts.trn++;
	    lgl->stats.prgss++;
	    if (red) lgl->stats.unhd.tauts.red++;
	    ntrnred++;
	    lglrmtwch (lgl, other, lit, other2, red);
	    lglrmtwch (lgl, other2, lit, other, red);
	    LOG (2, "removed %s ternary clause %d %d %d",
		 lglred2str (red), lit, other, other2);
	    lgldeclscnt (lgl, 3, red, 0);
	    assert (!lgl->dense);
	    q -= 2;
	  } else if (lglstr (lgl) && 
	             lglunhimplies2incl (dfpr, other2, lit)) {
TRNSTR:
	    LOG (2,
	         "unhiding removal of literal %d with implication "
		 "%d %d from ternary clause %d %d %d",
		 other2, other2, lit, lit, other, other2);
	    lgl->stats.unhd.str.trn++;
	    lgl->stats.prgss++;
	    if (red) lgl->stats.unhd.str.red++;
            ntrnstr++;
	    lglrmtwch (lgl, other, lit, other2, red);
	    lglrmtwch (lgl, other2, lit, other, red);
	    LOG (2, "removed %s ternary clause %d %d %d",
		 lglred2str (red), lit, other, other2);
	    lgldeclscnt (lgl, 3, red, 0);
	    if (!red) lgl->stats.irr++, assert (lgl->stats.irr > 0);
	    else lgl->stats.red.bin++, assert (lgl->stats.red.bin > 0);
	    delta = lglwchbin (lgl, other, lit, red);
	    if (delta) { p += delta, q += delta, eow += delta, w += delta; }
	    (--q)[-1] = red | BINCS | (other << RMSHFT);
#ifndef NLGLPICOSAT
	    lglpicosatchkclsarg (lgl, lit, other, 0);
#endif
	    continue;
	  } else if (lglstr (lgl) && lglunhimplies2incl (dfpr, other, lit)) {
	    SWAP (other, other2);
	    goto TRNSTR;
	  } else if (lgl->opts.unhdhbr.val &&
	             (root = lglunhroot (dfpr, -lit)) &&
	             !lglval (lgl, root)) {
	    if (root == lglunhroot (dfpr, -other2)) {
	      lca = lglunhlca (lgl, dfpr, -lit, -other2);
	    } else if (root == lglunhroot (dfpr, -other)) {
	      lca = lglunhlca (lgl, dfpr, -lit, -other);
	      SWAP (other, other2);
	    } else if (lglunhimplies2incl (dfpr, root, -other2)) lca = root;
	    else if (lglunhimplies2incl (dfpr, root, -other)) {
	      lca = root;
	      SWAP (other, other2);
	    } else continue;
	    assert (lca);
	    if (!lca) continue;//TODO remove?
	    if (abs (lca) == abs (lit)) continue;
	    if (abs (lca) == abs (other)) continue;
	    if (abs (lca) == abs (other2)) continue;
	    if (lglunhimplies2incl (dfpr, lca, other)) continue;
	    LOG (2,
	      "negations of literals %d %d in ternary clause %d %d %d "
	      "implied by %d", lit, other2, lit, other, other2, lca);
	    lgl->stats.unhd.hbrs.trn++;
	    if (red) lgl->stats.unhd.hbrs.red++;
	    lgl->stats.prgss++;
            ntrnhbrs++;
	    LOG (2, "unhidden hyper binary resolved clause %d %d",-lca,other);
#ifndef NLGLPICOSAT
	    lglpicosatchkclsarg (lgl, -lca, other, 0);
#endif
	    assert (lca != -lit);
	    lgl->stats.red.bin++, assert (lgl->stats.red.bin > 0);
	    delta = lglwchbin (lgl, -lca, other, REDCS);
	    if (delta) { p += delta, q += delta, eow += delta, w += delta; }
	    delta = lglwchbin (lgl, other, -lca, REDCS);
	    if (delta) { p += delta, q += delta, eow += delta, w += delta; }
	  }
	}
      }
      lglshrinkhts (lgl, hts, hts->count - (p - q));
    }
NEXTIDX:
    ;
  }
  if (nbinred) LOG (2, "unhiding %d tautological binary clauses", nbinred);
  if (nbinunits) LOG (2, "unhiding %d units in binary clauses", nbinunits);
  if (ntrnred) LOG (2, "unhiding %d tautological ternary clauses", ntrnred);
  if (ntrnstr) LOG (2, "unhiding %d strengthened ternary clauses", ntrnstr);
  if (ntrnunits) LOG (2, "unhiding %d units in ternary clauses", ntrnunits);
  if (ntrnstr)
     LOG (2, "unhidden %d hyper binary resolution from ternary clauses", ntrnhbrs);
  return 1;
}

static int lglcmpdfl (const DFL * a, const DFL * b) {
  return a->discovered - b->discovered;
}

static int lglunhideglue (LGL * lgl, const DFPR * dfpr, int glue, int irronly) {
  DFL * dfl, * eodfl, * d, * e; int szdfl, posdfl, negdfl, ndfl, res;
  int oldsize, newsize, hastobesatisfied, satisfied, tautological;
  int watched, lit, ulit, val, sign, nonfalse, root, lca, unit;
  int ntaut = 0, nstr = 0, nunits = 0, nhbrs = 0, lidx;
  int * p, * q, * c, * eoc, red;
  int lca1, lca2, root1, root2;
  Stk * lits;
  Lir * lir;
#ifndef NLGLOG
  char type[20];
  if (glue < 0) sprintf (type, "irredundant");
  else sprintf (type, "redundant glue %d", glue);
#endif
  assert (!lgl->mt);
  assert (-1 <= glue && glue < MAXGLUE);
  if (glue < 0) {
    lir = 0;
    lits = &lgl->irr;
    red = 0;
  } else {
    lir = lgl->red + glue;
    lits = &lir->lits;
    red = REDCS;
  }
  res = 1;
  dfl = 0; szdfl = 0;
  // go through all clauses of this glue and for each do:
  //
  //   SHRINK  simplify clause according to current assignment
  //   FAILED  check if is a hidden failed literal
  //   HTE     check if it is a hidden tautology
  //   STRNEG  remove hidden literals using complement literals
  //   STRPOS  remove hidden literals using positive literals
  //   HBR     perform unhiding hyper binary resolution
  //   NEXT    clean up, unwatch if necessary, reconnect bin/trn, bcp unit
  //
  for (c = lits->start; !lgl->mt && c < lits->top; c = eoc + 1) {
    if (lglterminate (lgl) || !lglsyncunits (lgl)) { res = 0; break; }
    if ((lit = *(eoc = c)) >= NOTALIT) continue;
    lgl->stats.unhd.steps++;
    lidx = c - lits->start;
    if (red) { lidx <<= GLUESHFT; lidx |= glue; }
    watched = 1;
    while (*eoc) eoc++;
    oldsize = eoc - c;

    unit = hastobesatisfied = satisfied = tautological = ndfl = 0;
//SHRINK: check satisfied + remove false literals + count visited
    q = c;
    nonfalse = posdfl = negdfl = 0;
    for (p = c; p < eoc; p++) {
      lit = *p;
      val = lglval (lgl, lit);
      if (val > 0) {
	satisfied = 1;
	q = c + 2;
	break;
      }
      if (val < 0) {
	if (p < c + 2) {
	  *q++ = lit;		// watched, so have to keep it
	  hastobesatisfied = 1;	// for assertion checking only
	}
	continue;
      }
      *q++ = lit;
      nonfalse++;
      if (dfpr[lglulit (lit)].discovered) posdfl++;	// count pos in BIG
      if (dfpr[lglulit (-lit)].discovered) negdfl++;	// count neg in BIG
    }
    *(eoc = q) = 0;
    assert (eoc - c >= 2);	// we assume bcp done before
    ndfl = posdfl + negdfl;	// number of literals in BIG
    if (hastobesatisfied) assert (satisfied);
    if (satisfied || ndfl < 2) goto NEXT;
    assert (nonfalse = eoc - c);
    assert (nonfalse >= negdfl);
//FAILED: find root implying all negated literals
    if (nonfalse != negdfl) goto HTE;	// not enough complement lits in BIG
    assert (c < eoc);
    root = lglunhroot (dfpr, -*c);
    if (lglval (lgl, root)) goto HTE;
    for (p = c + 1; p < eoc && lglunhroot (dfpr, -*p) == root; p++)
      ;
    if (p < eoc) goto HTE;		// at least two roots
    LOGCLS (2, c, "unhiding failed literal through large %s clause",type);
    LOG (2, "unhiding that all negations are implied by root %d", root);
    lca = -*c;
    for (p = c + 1; p < eoc; p++)
      lca = lglunhlca (lgl, dfpr, -*p, lca);
    assert (!lglval (lgl, lca));
    LOG (2, "unhiding failed large %s clause implied by LCA %d", type, lca);
    lgl->stats.unhd.failed.lrg++;
    unit = -lca;
    goto NEXT;  // otherwise need to properly unwatch and restart etc.
    		// which is too difficult to implement so leave further
		// simplification of this clause to next unhiding round
HTE:
    if (glue < 0 && !irronly) goto STRNEG; // skip tautology checking if
       					   // redundant clauses used and
					   // we work on irredundant clauses
    if (posdfl < 2 || negdfl < 2) goto STRNEG;
    if (ndfl > szdfl) { RSZ (dfl, szdfl, ndfl); szdfl = ndfl; }
    ndfl = 0;
    // copy all literals and their complements to 'dfl'
    for (p = c; p < eoc; p++) {
      for (sign = -1; sign <= 1; sign += 2) {
	lit = *p;
	ulit = lglulit (sign * lit);
	if (!dfpr[ulit].discovered) continue;	// not in BIG so skip
	assert (ndfl < szdfl);
	dfl[ndfl].discovered = dfpr[ulit].discovered;
	dfl[ndfl].finished = dfpr[ulit].finished;
	dfl[ndfl].sign = sign;
#ifndef NLGLOG
	dfl[ndfl].lit4logging = lit;
#endif
	ndfl++;
      }
    }
    lgl->stats.unhd.steps += 6;			// rough guess
    SORT (dfl, ndfl, lglcmpdfl);
    eodfl = dfl + ndfl;
    // Now check if there are two consecutive literals, the first
    // a complement of a literal in the clause, which implies another
    // literal actually occurring positive in the clause, where
    // 'd' ranges over complement literals
    // 'e' ranges over original literals
    for (d = dfl; d < eodfl - 1; d++)
      if (d->sign < 0) break;			// get first negative pos
    while (d < eodfl - 1) {
      assert (d->sign < 0);
      for (e = d + 1; e < eodfl && e->finished < d->finished; e++) {
	if (e->sign < 0) continue;		// get next positive pos
	assert (d->sign < 0 && e->sign > 0);
	assert (d->discovered <= e->discovered);
	assert (e ->finished <= d->finished);
	LOGCLS (2, c,
	        "unhiding with implication %d %d tautological %s clause",
		-d->lit4logging, e->lit4logging, type);
	ntaut++;
	lgl->stats.unhd.tauts.lrg++;
	if (red) lgl->stats.unhd.tauts.red++;
	lgl->stats.prgss++;
	tautological = 1;
	goto NEXT;
      }
      for (d = e; d < eodfl && d->sign > 0; d++)
	;
    }
STRNEG:
    if (!lglstr (lgl)) goto HBR;
    if (negdfl < 2) goto STRPOS;
    if (negdfl > szdfl) { RSZ (dfl, szdfl, negdfl); szdfl = negdfl; }
    lgl->stats.unhd.steps++;
    ndfl = 0;
    // copy complement literals to 'dfl'
    for (p = c; p < eoc; p++) {
      lit = *p;
      ulit = lglulit (-lit);			// NOTE: '-lit' not 'lit'
      if (!dfpr[ulit].discovered) continue;
      assert (ndfl < szdfl);
      dfl[ndfl].discovered = dfpr[ulit].discovered;	// of '-lit'
      dfl[ndfl].finished = dfpr[ulit].finished;		// of '-lit'
      dfl[ndfl].lit = lit;			// NOTE: but 'lit' here
      ndfl++;
    }
    if (ndfl < 2) goto STRPOS;
    lgl->stats.unhd.steps += 3;			// rough guess
    SORT (dfl, ndfl, lglcmpdfl);
    eodfl = dfl + ndfl;
    for (d = dfl; d < eodfl - 1; d = e) {
      assert (d->discovered);
      for (e = d + 1; e < eodfl && d->finished >= e->finished; e++) {
	assert (d->discovered <= e->discovered);
	lit = e->lit;
	LOGCLS (2, c,
		"unhiding removal of literal %d "
		"with implication %d %d from large %s clause",
		lit, -d->lit, -e->lit, type);
	e->lit = 0;
	nstr++;
	lgl->stats.unhd.str.lrg++;
	if (red) lgl->stats.unhd.str.red++;
	lgl->stats.prgss++;
	if (!watched) continue;
	if (lit != c[0] && lit != c[1]) continue;
	lglrmlwch (lgl, c[0], red, lidx);
	lglrmlwch (lgl, c[1], red, lidx);
	watched = 0;
      }
    }
    assert (eoc - c >= 1 );
    q = c;
    if (watched) q += 2;			// keep watched literals
      						// if we still watch
    // move non BIG literals
    for (p = q; p < eoc; p++) {
      lit = *p;
      ulit = lglulit (-lit);			// NOTE: '-lit' not 'lit'
      if (dfpr[ulit].discovered) continue;
      *q++ = lit;
    }
    // copy from 'dfl' unremoved BIG literals back to clause
    for (d = dfl; d < eodfl; d++) {
      lit = d->lit;
      if (!lit) continue;
      if (watched && lit == c[0]) continue;
      if (watched && lit == c[1]) continue;
      *q++ = lit;
    }
    *(eoc = q) = 0;
STRPOS:
    if (posdfl < 2) goto HBR;
    if (posdfl > szdfl) { RSZ (dfl, szdfl, posdfl); szdfl = posdfl; }
    ndfl = 0;
    // copy original literals to 'dfl' but sort reverse wrt 'discovered'
    for (p = c; p < eoc; p++) {
      lit = *p;
      ulit = lglulit (lit);			// NOTE: now 'lit'
      if (!dfpr[ulit].discovered) continue;
      assert (ndfl < szdfl);
      dfl[ndfl].discovered = -dfpr[ulit].discovered;	// of 'lit'
      dfl[ndfl].finished = -dfpr[ulit].finished;		// of 'lit'
      dfl[ndfl].lit = lit;
      ndfl++;
    }
    if (ndfl < 2) goto NEXT;
    lgl->stats.unhd.steps += 3;			// rough guess
    SORT (dfl, ndfl, lglcmpdfl);
    eodfl = dfl + ndfl;
    for (d = dfl; d < eodfl - 1; d = e) {
      assert (d->discovered);
      for (e = d + 1; e < eodfl && d->finished >= e->finished; e++) {
	assert (d->discovered <= e->discovered);
	lit = e->lit;
	LOGCLS (2, c,
		"unhiding removal of literal %d "
		"with implication %d %d from large %s clause",
		lit, e->lit, d->lit, type);
	e->lit = 0;
	nstr++;
	lgl->stats.unhd.str.lrg++;
	if (red) lgl->stats.unhd.str.red++;
	lgl->stats.prgss++;
	if (!watched) continue;
	if (lit != c[0] && lit != c[1]) continue;
	lglrmlwch (lgl, c[0], red, lidx);
	lglrmlwch (lgl, c[1], red, lidx);
	watched = 0;
      }
    }
    assert (eoc - c >= 1 );
    q = c;
    if (watched) q += 2;
    for (p = q; p < eoc; p++) {
      lit = *p;
      ulit = lglulit (lit);			// NOTE: now 'lit'
      if (dfpr[ulit].discovered) continue;
      *q++ = lit;
    }
    for (d = dfl; d < eodfl; d++) {
      lit = d->lit;
      if (!lit) continue;
      if (watched && lit == c[0]) continue;
      if (watched && lit == c[1]) continue;
      *q++ = lit;
    }
    *(eoc = q) = 0;
HBR:
    if (!lgl->opts.unhdhbr.val) goto NEXT;
    if (eoc - c < 3) goto NEXT;
    root1 = root2 = lca1 = lca2 = 0;
    for (p = c; (lit = *p); p++) {
      root = lglunhroot (dfpr, -lit);
      if (!root) root = -lit;
      if (!root1) { root1 = root; continue; }
      if (root1 == root) continue;
      if (!root2) { root2 = root; continue; }
      if (root2 == root) continue;
      if (lglunhimplies2incl (dfpr, root1, -lit)) { lca1 = root1; continue; }
      if (lglunhimplies2incl (dfpr, root2, -lit)) { lca2 = root2; continue; }
      goto NEXT;			// else more than two roots ...
    }
    assert (root1);
    if (!root2) goto NEXT;
    if (root1 == -root2) goto NEXT;
    if (lglunhimplies2incl (dfpr, root1, -root2)) goto NEXT;
    LOGCLS (2, c, "root hyper binary resolution %d %d of %s clause",
	    -root1, -root2, type);
    if (!lca1 && !lca2) {
      for (p = c; (lit = *p); p++) {
	root = lglunhroot (dfpr, -lit);
	if (root) {
	  if (root == root1)
	    lca1 = lca1 ? lglunhlca (lgl, dfpr, lca1, -lit) : -lit;
	  if (root == root2)
	    lca2 = lca2 ? lglunhlca (lgl, dfpr, lca2, -lit) : -lit;
	} else {
	  assert (!lca2);
	  if (lca1) lca2 = -lit; else lca1 = -lit;
	}
      }
    } else {
      if (!lca1) lca1 = root1;
      if (!lca2) lca2 = root2;
    }
    if (lca1 == -lca2) goto NEXT;
    if (lglunhimplies2incl (dfpr, lca1, -lca2)) goto NEXT;
    LOGCLS (2, c, "lca hyper binary resolution %d %d of %s clause",
	    -lca1, -lca2, type);
    lgl->stats.unhd.hbrs.lrg++;
    if (red) lgl->stats.unhd.hbrs.red++;
#ifndef NLGLPICOSAT
    lglpicosatchkclsarg (lgl, -lca1, -lca2, 0);
#endif
    lglwchbin (lgl, -lca1, -lca2, REDCS);
    lglwchbin (lgl, -lca2, -lca1, REDCS);
    lgl->stats.red.bin++;
    assert (lgl->stats.red.bin > 0);
NEXT:
    newsize = eoc - c;
    assert (satisfied || tautological || newsize >= 1);
    if (newsize <= 3 || satisfied || tautological) {
      lgldeclscnt (lgl, 4, red, glue);
      if (watched) {
	lglrmlwch (lgl, c[0], red, lidx);
	lglrmlwch (lgl, c[1], red, lidx);
      }
    }
    assert (!*eoc);
    for (p = c + oldsize; p > eoc; p--) *p = REMOVED;
    if (satisfied || tautological) {
      while (p >= c) *p-- = REMOVED;
      if (red) { lglchkact (c[-1]); c[-1] = REMOVED; }
      eoc = c + oldsize;
      continue;
    }
#ifndef NLGLPICOSAT
    if (newsize < oldsize) lglpicosatchkclsaux (lgl, c);
#endif
    if (red && newsize <= 3) { lglchkact (c[-1]); c[-1] = REMOVED; }
    if (newsize > 3 && !watched) {
      (void) lglwchlrg (lgl, c[0], c[1], red, lidx);
      (void) lglwchlrg (lgl, c[1], c[0], red, lidx);
    } else if (newsize == 3) {
      LOGCLS (2, c, "large %s clause became ternary", type);
      lglwchtrn (lgl, c[0], c[1], c[2], red);
      lglwchtrn (lgl, c[1], c[0], c[2], red);
      lglwchtrn (lgl, c[2], c[0], c[1], red);
      if (!red) lgl->stats.irr++, assert (lgl->stats.irr > 0);
      else lgl->stats.red.trn++, assert (lgl->stats.red.trn > 0);
      c[0] = c[1] = c[2] = *eoc = REMOVED;
    } else if (newsize == 2) {
      LOGCLS (2, c, "large %s clause became binary", type);
      lglwchbin (lgl, c[0], c[1], red);
      lglwchbin (lgl, c[1], c[0], red);
      if (!red) lgl->stats.irr++, assert (lgl->stats.irr > 0);
      else lgl->stats.red.bin++, assert (lgl->stats.red.bin > 0);
      c[0] = c[1] = *eoc = REMOVED;
    } else if (newsize == 1) {
      LOGCLS (2, c, "large %s clause became unit", type);
      unit = c[0];		// even works if unit already set
      c[0] = *eoc = REMOVED;
      lgl->stats.unhd.units.lrg++;
      nunits++;
    }
    if (!unit) continue;
    lglunit (lgl, unit);
    if (lglbcp (lgl)) continue;
    assert (!lgl->mt);
    lgl->mt = 1;
    LOG (1, "unhiding large clause produces empty clause");
    res = 0;
  }
  if (nunits)
    LOG (1, "unhiding %d units from large %s clauses", nunits, type);
  if (ntaut)
    LOG (1, "unhiding %d large tautological %s clauses", ntaut, type);
  if (nstr)
    LOG (1, "unhiding removal of %d literals in %s clauses", nstr, type);
  if (nhbrs)
    LOG (1, "unhiding %d hyper binary resolutions in %s clauses", nhbrs, type);
  if (dfl) DEL (dfl, szdfl);
  return res;
}

static void lglfixlrgwchs (LGL * lgl) {
  int idx, sign, lit, blit, tag, red, lidx, fixed;
  const int * p, * eow, * c;
  int * q, * w;
  HTS * hts;
  fixed = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = lglhts (lgl, lit);
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      q = w;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == BINCS) { *q++ = blit; continue; }
	lidx = *++p;
	if (tag == TRNCS) { *q++ = blit; *q++ = lidx; continue; }
	assert (tag == LRGCS);
	red = blit & REDCS;
	c = lglidx2lits (lgl, red, lidx);
	if (*c >= NOTALIT) { fixed++; continue; }
	*q++ = blit;
	*q++ = lidx;
      }
      lglshrinkhts (lgl, hts, hts->count - (p - q));
    }
  }
  assert (!(fixed & 1));
  if (fixed) LOG (1, "fixed %d large watches", fixed);
}

static int lglunhidelrg (LGL * lgl, const DFPR * dfpr, int irronly) {
  int glue, res = 1;
  for (glue = -1; res && glue < MAXGLUE; glue++)
    res = lglunhideglue (lgl, dfpr, glue, irronly);
  lglfixlrgwchs (lgl);
  return res;
}

static int lglunhdunits (LGL * lgl) {
  int res = lgl->stats.unhd.units.bin;
  res += lgl->stats.unhd.units.trn;
  res += lgl->stats.unhd.units.lrg;
  return res;
}

static int lglunhdfailed (LGL * lgl) {
  int res = lgl->stats.unhd.stamp.failed;
  res += lgl->stats.unhd.failed.lits;
  res += lgl->stats.unhd.failed.bin;
  res += lgl->stats.unhd.failed.trn;
  res += lgl->stats.unhd.failed.lrg;
  return res;
}

static int lglunhdhbrs (LGL * lgl) {
  int res = lgl->stats.unhd.hbrs.trn;
  res += lgl->stats.unhd.hbrs.lrg;
  return res;
}

static int lglunhdtauts (LGL * lgl) {
  int res = lgl->stats.unhd.stamp.trds;
  res += lgl->stats.unhd.tauts.bin;
  res += lgl->stats.unhd.tauts.trn;
  res += lgl->stats.unhd.tauts.lrg;
  return res;
}

static int lglunhdstrd (LGL * lgl) {
  int res = lgl->stats.unhd.units.bin;	// shared!
  res += lgl->stats.unhd.str.trn;
  res += lgl->stats.unhd.str.lrg;
  return res;
}

static void lglrmbindup (LGL * lgl) {
  int idx, sign, lit, blit, tag, red, other, round, redrem, irrem;
  int * w, * eow, * p, * q;
  HTS * hts;
  redrem = irrem = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      assert (lglmtstk (&lgl->seen));
      for (round = 0; round < 2; round++) {
	hts = lglhts (lgl, lit);
	w = lglhts2wchs (lgl, hts);
	eow = w + hts->count;
	q = w;
	for (p = w; p < eow; p++) {
	  blit = *p;
	  tag = blit & MASKCS;
	  if (tag != BINCS) *q++ = blit;
	  if (tag== LRGCS || tag == TRNCS) *q++ = *++p;
	  if (tag != BINCS) continue;
	  red = blit & REDCS;
	  other = blit >> RMSHFT;
	  if (lglsignedmarked (lgl, other)) {
	    if (round && !red) goto ONLYCOPY;
	    if (red) redrem++; else irrem++;
	    if (abs (lit) > abs (other)) {
	      LOG (2, 
		"removing duplicated %s binary clause %d %d and 2nd watch %d",
		lglred2str (red), lit, other, other);
	      lgldeclscnt (lgl, 2, red, 0);
	      if (!red && lgl->dense) 
		lgldecocc (lgl, lit), lgldecocc (lgl, other);
	      lgl->stats.bindup.removed++;
	      if (red) lgl->stats.bindup.red++;
	    } else 
	      LOG (2, 
	        "removing 1st watch %d of duplicated %s binary clause %d %d",
	        other, lglred2str (red), other, lit);
	  } else {
	    if ((!round && !red) || (round && red))
	      lglsignedmarknpushseen (lgl, other);
ONLYCOPY:
	    *q++ = blit;
	  }
	}
	lglshrinkhts (lgl, hts, hts->count - (p - q));
      }
      lglpopnunmarkstk (lgl, &lgl->seen);
    }
  }
  assert (!(irrem & 1));
  assert (!(redrem & 1));
}

#define UNHDVL 2 // should stay 2

static DFPR * lglstampall (LGL * lgl, int irronly) {
  int roots, searches, noimpls, unassigned, visited;
  unsigned pos, delta, mod, ulit, first, last, count;
  int root, stamp, rootsonly, lit;
  Stk units, sccs, trds;
  DFOPF * dfopf, * q;
  DFPR * dfpr;
  Wtk work;
  Val val;
  if (lgl->nvars <= 2) return 0;
  lglrmbindup (lgl);
  NEW (dfpr, 2*lgl->nvars);
  NEW (dfopf, 2*lgl->nvars);
  CLR (work); CLR (sccs); CLR (trds); CLR (units);
  for (q = dfopf; q < dfopf + 2*lgl->nvars; q++) q->pushed = -1;
  searches = roots = noimpls = unassigned = stamp = visited = 0;
  for (rootsonly = 1; rootsonly >= 0; rootsonly--) {
    count = 0;
    first = mod = 2*(lgl->nvars - 2);
    assert (mod > 0);
    pos = lglrand (lgl) % mod;
    delta = lglrand (lgl) % mod;
    if (!delta) delta++;
    while (lglgcd (delta, mod) > 1)
      if (++delta == mod) delta = 1;
    LOG (2, "unhiding %s round start %u delta %u mod %u",
	 (rootsonly ? "roots-only": "non-root"), pos, delta, mod);
    for (;;) {
      if (lglterminate (lgl)) { searches = 0; goto DONE; }
      if (!lglsyncunits (lgl)) { assert (lgl->mt); goto DONE; }
      ulit = pos + 4;
      root = lglilit (ulit);
      lgl->stats.unhd.steps++;
      count++;
      if (lglval (lgl, root)) goto CONTINUE;
      if (rootsonly) unassigned++;
      if (dfpr[lglulit (root)].discovered) goto CONTINUE;
      if (rootsonly &&
	  !lglunhdisroot (lgl, root, dfpr, irronly)) goto CONTINUE;
      if (!lglunhdhasbins (lgl, dfpr, -root, irronly)) {
	if (rootsonly) noimpls++; goto CONTINUE;
      }
      if (rootsonly) roots++;
      searches++;
      assert (lglmtstk (&units));
      stamp = lglstamp (lgl, root, dfpr, dfopf,
			&work, &units, &sccs, &trds, &visited,
			stamp, irronly);
      while (!lglmtstk (&units)) {
	lit = lglpopstk (&units);
	val = lglval (lgl, lit);
	if (val > 0) continue;
	if (val < 0) {
	  assert (!lgl->mt);
	  LOG (1, "unhidding stamp unit %d already false", lit);
	  lgl->mt = 1;
	  goto DONE;
	}
	lglunit (lgl, lit);
	if (!lglbcp (lgl)) {
	  assert (!lgl->mt);
	  LOG (1, "propagating unhidden stamp unit %d failed", lit);
	  lgl->mt = 1;
	  goto DONE;
	}
      }
CONTINUE:
      last = pos;
      pos += delta;
      if (pos >= mod) pos -= mod;
      if (pos == first) { assert (count == mod); break; }
      if (mod == 1) break;
      if (first == mod) first = last;
    }
  }
  assert (searches >= roots);
  lglprt (lgl, UNHDVL,
	  "[unhd-%d-%d] %d unassigned variables out of %d (%.0f%%)",
	  lgl->stats.unhd.count, lgl->stats.unhd.rounds,
	  lgl->unassigned, lgl->nvars - 2,
	    lglpcnt (lgl->unassigned, lgl->nvars - 2));
  lglprt (lgl, UNHDVL,
	  "[unhd-%d-%d] %d root literals out of %d (%.0f%%)",
	  lgl->stats.unhd.count, lgl->stats.unhd.rounds,
	  roots, unassigned, lglpcnt (roots, unassigned));
  lglprt (lgl, UNHDVL,
    "[unhd-%d-%d] %d additional non-root searches out of %d (%.0f%%)",
	  lgl->stats.unhd.count, lgl->stats.unhd.rounds,
	  searches - roots, unassigned,
	    lglpcnt (searches - roots, unassigned));
  lglprt (lgl, UNHDVL,
	  "[unhd-%d-%d] %d literals not in F2 out of %d (%.0f%%)",
	  lgl->stats.unhd.count, lgl->stats.unhd.rounds,
	  noimpls, unassigned, lglpcnt (noimpls, unassigned));
  lglprt (lgl, UNHDVL,
	  "[unhd-%d-%d] %d visited literals out of %d (%.0f%%)",
	  lgl->stats.unhd.count, lgl->stats.unhd.rounds,
	  visited, unassigned, lglpcnt (visited, unassigned));
  lglprt (lgl, UNHDVL,
	  "[unhd-%d-%d] %.2f average number visited literals per search",
	  lgl->stats.unhd.count, lgl->stats.unhd.rounds,
	  lglavg (visited, searches));
DONE:
  if (!searches || lgl->mt) { DEL (dfpr, 2*lgl->nvars); dfpr = 0; }
  lglrelwtk (lgl, &work);
  lglrelstk (lgl, &units);
  lglrelstk (lgl, &sccs);
  lglrelstk (lgl, &trds);
  DEL (dfopf, 2*lgl->nvars);
  return dfpr;
}

static int lglunhide (LGL * lgl) {
  int64_t limit, oldprgss = lgl->stats.prgss, roundprgss = 0;
  int irronly, round, maxrounds, noprgssrounds, success;
  int oldunits, oldfailed, oldtauts, oldhbrs, oldstrd;
  DFPR * dfpr = 0;
  assert (lgl->opts.unhide.val);
  if (lgl->nvars <= 2) return 1;
  lgl->stats.unhd.count++;
  assert (!lgl->unhiding);
  lgl->unhiding = 1;
  lglstart (lgl, &lgl->stats.tms.unhd);
  irronly = !lgl->stats.red.bin || (lgl->stats.unhd.count & 1);
  if (lgl->level > 0) lglbacktrack (lgl, 0);
  if (lgl->stats.unhd.count == 1) limit = lgl->opts.unhdmaxeff.val/10;
  else limit = (lgl->opts.unhdreleff.val*lgl->stats.visits.search)/1000;
  maxrounds = lgl->opts.unhdroundlim.val;
  if (lgl->stats.unhd.count == 1) maxrounds *= 4;
  if (lgl->stats.unhd.count == 2) maxrounds *= 2;
  if (limit < lgl->opts.unhdmineff.val) limit = lgl->opts.unhdmineff.val;
  if (limit > lgl->opts.unhdmaxeff.val) limit = lgl->opts.unhdmaxeff.val;
  LOG (2, "unhiding penalty %d", lgl->limits.unhd.pen);
  if (lgl->limits.unhd.pen < 0) limit <<= -lgl->limits.unhd.pen;
  if (lgl->limits.unhd.pen > 0) limit >>= lgl->limits.unhd.pen;
  LOG (2, "unhiding with up to %lld search steps", limit);
  lgl->limits.unhd.steps = lgl->stats.unhd.steps + limit;
  oldunits = lglunhdunits (lgl);
  oldfailed = lglunhdfailed (lgl);
  oldtauts = lglunhdtauts (lgl);
  oldhbrs = lglunhdhbrs (lgl);
  oldstrd = lglunhdstrd (lgl);
  noprgssrounds = round = 0;
  while (!lgl->mt) {
    if (round >= maxrounds) break;
    if (round > 0) {
      if (roundprgss == lgl->stats.prgss) {
	if (noprgssrounds++ == lgl->opts.unhdlnpr.val) {
	  LOG (1, "too many non progress unhiding rounds");
	  break;
	}
      }
    }
    round++;
    roundprgss = lgl->stats.prgss;
    lgl->stats.unhd.rounds++;
    lglgc (lgl);
    if (!lgl->nvars || lgl->mt) break;
    assert (!dfpr);
    dfpr = lglstampall (lgl, irronly);
    if (!dfpr) break;
    if (!lglunhidefailed (lgl, dfpr)) break;
    if (!lglunhidebintrn (lgl, dfpr, irronly)) break;
    if (!lglunhidelrg (lgl, dfpr, irronly)) break;
    if (lgl->stats.unhd.steps >= limit) break;
    irronly = !lgl->stats.red.bin || !irronly;
    DEL (dfpr, 2*lgl->nvars);
    assert (!dfpr);
  }
  if (dfpr) DEL (dfpr, 2*lgl->nvars);
  lglprt (lgl, UNHDVL,
	  "[unhd-%d-%d] %d units, %d failed, %d tauts, %d hbrs, %d literals",
	  lgl->stats.unhd.count, lgl->stats.unhd.rounds,
	  lglunhdunits (lgl) - oldunits,
	  lglunhdfailed (lgl) - oldfailed,
	  lglunhdtauts (lgl) - oldtauts,
	  lglunhdhbrs (lgl) - oldhbrs,
	  lglunhdstrd (lgl) - oldstrd);
  success = (oldprgss < lgl->stats.prgss);
  if (success && lgl->limits.unhd.pen > MINPEN) lgl->limits.unhd.pen--;
  if (!success && lgl->limits.unhd.pen < MAXPEN) lgl->limits.unhd.pen++;
  assert (lgl->unhiding);
  lgl->unhiding = 0;
  lglrep (lgl, 1, 'u');
  lglstop (lgl);
  lgl->limits.unhd.cinc += lgl->opts.unhdcintinc.val;
  lgl->limits.unhd.vinc += lgl->opts.unhdvintinc.val;
  lgl->limits.unhd.visits = lgl->stats.visits.search + lgl->limits.unhd.vinc;
  lgl->limits.unhd.confs = lgl->stats.confs + lgl->limits.unhd.cinc;
  lgl->limits.unhd.irr = lgl->stats.irr + lgl->opts.unhdirrintinc.val;
  lgl->limits.unhd.prgss = lgl->stats.prgss;
  return !lgl->mt;
}

static int lglpartrepr (LGL * lgl, int lit) {
  int res, tmp, next;
  AVar * av;
  lit = abs (lit);
  for (res = lit; (av = lglavar (lgl, res))->part != res; res = av->part)
    ;
  for (tmp = lit; tmp != res; tmp = next) {
    av = lglavar (lgl, tmp);
    next = av->part;
    av->part = res;
  }
  return res;
}

static void lglpartmerge (LGL * lgl, int a, int b) {
  int r = lglpartrepr (lgl, a), s = lglpartrepr (lgl, b);
  if (r < s) lglavar (lgl, s)->part = r;
  else if (r > s) lglavar (lgl, r)->part = s;
}

static int lglcmpart (const Part * a, const Part * b) {
  int res;
  if ((res = (a->clauses <= 1) - (b->clauses <= 1))) return res;
  if ((res = a->sat - b->sat)) return res;
  if ((res = a->vars - b->vars)) return res;
  if ((res = a->clauses - b->clauses)) return res;
  return a->orig - b->orig;
}

static Val lglphase (LGL * lgl, int lit) {
  Val res = lglavar (lgl, lit)->phase;
  if (lit < 0) res = -res;
  return res;
}

static void lglpart (LGL * lgl) {
  int i, idx, sign, lit, blit, red, tag, other, other2, count, sat, litsat;
  const int * w, * eow, * p, * c;
  Part * parts, * part;
  AVar * av, * bv;
  int nontriv;
  Stk partstk;
  HTS * hts;
  lglstart (lgl, &lgl->stats.tms.part);
  CLR (partstk);
  assert (lgl->opts.partition.val);
  for (idx = 2; idx < lgl->nvars; idx++) lgl->avars[idx].part = idx;
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign*idx;
      hts = lglhts (lgl, lit);
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (tag == LRGCS) continue;
	red = blit & REDCS;
	if (red) continue;
	other = blit >> RMSHFT;
	if (abs (other) < idx) continue;
	if (tag == TRNCS) {
	  if (abs (other2 = *p) < idx) continue;
	  lglpartmerge (lgl, lit, other2);
	} else assert (tag == BINCS);
	lglpartmerge (lgl, lit, other);
      }
    }
  for (c = lgl->irr.start; c < lgl->irr.top; c = p + 1) {
    if (*(p = c) >= NOTALIT) continue;
    lit =  *p;
    while ((other = *++p)) lglpartmerge (lgl, lit, other);
  }
  for (idx = 2; idx < lgl->nvars; idx++) (void) lglpartrepr (lgl, idx);
  count = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    av = lglavar (lgl, idx);
    if (av->part == idx) {
      assert (count == lglcntstk (&partstk));
      lglpushstk (lgl, &partstk, 1);
      av->part = count++;
    } else {
      bv = lglavar (lgl, av->part);
      assert (bv->part < count);
      av->part = bv->part;
      partstk.start[bv->part]++;
    }
  }
  NEW (parts, count);
  for (i = 0; i < count; i++) {
    part = parts + i;
    part->orig = i;
    part->sat = 1;
    part->vars = lglpeek (&partstk, i);
    part->clauses = 0;
  }
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign*idx;
      hts = lglhts (lgl, lit);
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      litsat = (lglphase (lgl, lit) > 0);
      av = lglavar (lgl, lit);
      part = parts + av->part;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (tag == LRGCS) continue;
	red = blit & REDCS;
	if (red) continue;
	other = blit >> RMSHFT;
	if (abs (other) < idx) continue;
	sat = litsat;
	if (tag == TRNCS) {
	  if (abs (other2 = *p) < idx) continue;
	  if (!sat && lglphase (lgl, other2) > 0) sat = 1;
	}
	if (!sat) sat = (lglphase (lgl, other) > 0);
	if (!sat) part->sat = 0;
	part->clauses++;
      }
    }
  for (c = lgl->irr.start; c < lgl->irr.top; c = p + 1) {
    if ((lit = *(p = c)) >= NOTALIT) continue;
    sat = (lglphase (lgl, lit) > 0);
    part = parts + lglavar (lgl, lit)->part;
    while ((other = *++p))
      if (!sat && lglphase (lgl, other) > 0) sat = 1;
    if (!sat) part->sat = 0;
    part->clauses++;
  }
  SORT (parts, count, lglcmpart);
  nontriv = 0;
  for (i = 0; i < count; i++) if (parts[i].clauses > 1) nontriv++;
  if (lgl->stats.part.max < nontriv) lgl->stats.part.max = nontriv;
  lgl->stats.part.sum += nontriv;
  lglprt (lgl, 2, "[part-%d] found %d non-trivial connected components",
          lgl->stats.part.count, nontriv);
  if (lgl->opts.verbose.val)
    for (i = 0; i < count; i++) {
      part = parts + i;
      if (part->clauses <= 1) continue;
      lglprt (lgl, 2, "[part-%d] %d : %d vars, %d clauses, orig %d, %s",
              lgl->stats.part.count, i,
              part->vars, part->clauses, part->orig,
	      part->sat ? "satisfied" : "unsatisfied");
    }
  for (i = 0; i < count; i++) {
    part = parts + i;
    lglpoke (&partstk, part->orig, part->sat ? INT_MAX : i);
  }
  DEL (parts, count);
  for (idx = 2; idx < lgl->nvars; idx++) {
    av = lglavar (lgl, idx);
    av->part = lglpeek (&partstk, av->part);
  }
  lglrelstk (lgl, &partstk);
  lgldreschedule (lgl);
  lgl->stats.part.count++;
  lgl->limits.part.vinc += lgl->opts.partvintinc.val;
  lgl->limits.part.cinc += lgl->opts.partcintinc.val;
  lgl->limits.part.visits = lgl->stats.visits.search + lgl->limits.part.vinc;
  lgl->limits.part.confs = lgl->stats.confs + lgl->limits.part.cinc;
  lglrep (lgl, 1, 'a');
  lgl->partitioned = 1;
  lgl->activepart = 0;
  lglstop (lgl);
}

static int lglcollecting (LGL * lgl) {
  if (lgl->stats.irr <= lgl->limits.gc.irr) {
    if (lgl->stats.visits.search <= lgl->limits.gc.visits) return 0;
    if (lgl->stats.confs <= lgl->limits.gc.confs) return 0;
  }
  return lgl->stats.fixed.current;
}

static int lglprobing (LGL * lgl) {
  if (!lgl->opts.probe.val) return 0;
  if (lgl->stats.irr > lgl->limits.prb.irr) return 1;
  if (lgl->stats.prgss <= lgl->limits.prb.prgss) return 0;
  if (lgl->stats.prgss > 2*lgl->limits.prb.prgss) return 1;
  if (lgl->stats.confs <= lgl->limits.prb.confs) return 0;
  return lgl->stats.visits.search >= lgl->limits.prb.visits;
}

static int lgldistilling (LGL * lgl) {
  if (!lgl->opts.distill.val) return 0;
  if (!lglstr (lgl)) return 0;
  if (lgl->stats.irr > lgl->limits.dst.irr) return 1;
  if (lgl->stats.prgss <= lgl->limits.dst.prgss) return 0;
  if (lgl->stats.prgss > 2*lgl->limits.dst.prgss) return 1;
  if (lgl->stats.confs <= lgl->limits.dst.confs) return 0;
  return lgl->stats.visits.search >= lgl->limits.dst.visits;
}

static int lgltreducing (LGL * lgl) {
  if (!lgl->opts.transred.val) return 0;
  if (lgl->stats.irr > lgl->limits.trd.irr) return 1;
  if (lgl->stats.prgss <= lgl->limits.trd.prgss) return 0;
  if (lgl->stats.prgss > 2*lgl->limits.trd.prgss) return 1;
  if (lgl->stats.confs <= lgl->limits.trd.confs) return 0;
  return lgl->stats.visits.search >= lgl->limits.trd.visits;
}

static int lglunhiding (LGL * lgl) {
  if (!lgl->opts.unhide.val) return 0;
  if (lgl->stats.irr > lgl->limits.unhd.irr) return 1;
  if (lgl->stats.prgss <= lgl->limits.unhd.prgss) return 0;
  if (lgl->stats.prgss > 2*lgl->limits.unhd.prgss) return 1;
  if (lgl->stats.confs <= lgl->limits.unhd.confs) return 0;
  return lgl->stats.visits.search >= lgl->limits.unhd.visits;
}

static int lgldecomposing (LGL * lgl) {
  if (!lgl->opts.decompose.val) return 0;
  if (!lglsmall (lgl)) return 0;
  if (lgl->stats.irr > lgl->limits.dcp.irr) return 1;
  if (lgl->stats.prgss <= lgl->limits.dcp.prgss) return 0;
  if (lgl->stats.prgss > 2*lgl->limits.dcp.prgss) return 1;
  if (lgl->stats.confs <= lgl->limits.dcp.confs) return 0;
  return lgl->stats.visits.search >= lgl->limits.dcp.visits;
}

static int lglifting (LGL * lgl) {
  if (!lgl->opts.lift.val) return 0;
  if (!lglsmall (lgl)) return 0;
  if (lgl->stats.irr > lgl->limits.lft.irr) return 1;
  if (lgl->stats.prgss <= lgl->limits.lft.prgss) return 0;
  if (lgl->stats.prgss > 2*lgl->limits.lft.prgss) return 1;
  if (lgl->stats.confs <= lgl->limits.lft.confs) return 0;
  return lgl->stats.visits.search >= lgl->limits.lft.visits;
}

static int lglpartitioning (LGL * lgl) {
  if (!lgl->opts.partition.val) return 0;
  if (lgl->stats.confs <= lgl->limits.part.confs) return 0;
  return lgl->stats.visits.search >= lgl->limits.part.visits;
}

static int lgleliminating (LGL * lgl) {
  if (!lgl->opts.elim.val) return 0;
  if (!lglsmall (lgl)) return 0;
  if (lgl->stats.irr > lgl->limits.elm.irr) return 1;
  if (lgl->stats.prgss <= lgl->limits.elm.prgss) return 0;
  if (lgl->stats.prgss > 2*lgl->limits.elm.prgss) return 1;
  if (lgl->stats.confs <= lgl->limits.elm.confs) return 0;
  return lgl->stats.visits.search >= lgl->limits.elm.visits;
}

static int lglreducing (LGL * lgl) {
  return lgl->stats.red.lrg >= lgl->limits.reduce;
}

static int lgldefragmenting (LGL * lgl) {
  int relfree;
  if (lgl->stats.pshwchs < lgl->limits.dfg.pshwchs) return 0;
  if (!lgl->nvars) return 0;
  relfree = (100 * lgl->nfreewchs + 99) / lgl->nvars;
  return relfree >= lgl->opts.defragfree.val;
}

static int lglrestarting (LGL * lgl) {
  if (!lgl->opts.restart.val) return 0;
  if (lgl->level <= 1) return 0;
  return lgl->stats.confs >= lgl->limits.restart.confs;
}

static int lglrebiasing (LGL * lgl) {
  if (!lgl->opts.rebias.val) return 0;
  return lgl->stats.confs >= lgl->limits.rebias.confs;
}

static int lglrephrasing (LGL * lgl) {
  if (!lgl->opts.rephrase.val) return 0;
  return lgl->stats.confs >= lgl->limits.rephrase;
}

static int lglfailed (LGL * lgl) {
  int val;
  assert (!lgl->mt && !lgl->failed);
  if (lgl->level > 0) return 0;
  if (!lgl->assume) return 0;
  val = lglcval (lgl, lgl->assume);
  if (val >= 0) return 0;
  LOG (2, "failed internal assumption %d", lgl->assume);
  lgl->failed = lgl->assume;
  return 1;
}

static int lglsimpaux (LGL * lgl) {
  if (lglreducing (lgl)) lglreduce (lgl);
  if (lglterminate (lgl)) return 1;
  if (lgldefragmenting (lgl)) lgldefrag (lgl);
  if (lgl->level > 0) goto REST;
  if (lglterminate (lgl)) return 1;
  if (lglunhiding (lgl) && !lglunhide (lgl)) return 0;
  if (lglterminate (lgl)) return 1;
  if (lglprobing (lgl) && !lglprobe (lgl)) return 0;
  if (lglterminate (lgl)) return 1;
  if (lgldistilling (lgl) && !lgldistill (lgl)) return 0;
  if (lglterminate (lgl)) return 1;
  if (lglifting (lgl) && !lglift (lgl)) return 0;
  if (lglterminate (lgl)) return 1;
  if (lgldecomposing (lgl) && !lgldecomp (lgl)) return 0;
  if (lglterminate (lgl)) return 1;
  if (lgltreducing (lgl) && !lgltrd (lgl)) return 0;
  if (lglterminate (lgl)) return 1;
  if (lgleliminating (lgl) && !lglelim (lgl)) return 0;
  if (lglterminate (lgl)) return 1;
  if (lglcollecting (lgl)) lglgc (lgl);
REST:
  if (lglterminate (lgl)) return 1;
  if (lglpartitioning (lgl)) lglpart (lgl);
  if (lglterminate (lgl)) return 1;
  if (lglrebiasing (lgl)) lglrebias (lgl);
  if (lglterminate (lgl)) return 1;
  if (lglrephrasing (lgl)) lglrephrase (lgl);
  return 1;
}

static int lglsimp (LGL * lgl) {
  int res;
  assert (!lgl->simplifying);
  lgl->simplifying = 1;
  res = lglsimpaux (lgl);
  assert (lgl->simplifying);
  lgl->simplifying = 0;
  return res;
}

static int lglbcptop (LGL * lgl) {
  int tmp;
  if (lglbcp (lgl)) return 1;
  tmp = lglana (lgl);
  assert (!tmp && lgl->mt);
  return 0;
}

static int lglcdcl (LGL * lgl) {
  for (;;) {
    if (lglbcpsearch (lgl) && lglsimp (lgl)) {
      if (lglterminate (lgl)) return 0;
      if (!lglsyncunits (lgl)) return 20;
      if (lglrestarting (lgl)) { lglrestart (lgl); continue; }
      if (!lgl->level && lglfailed (lgl)) return 20;
      if (!lgldecide (lgl)) return 10;
    } else if (!lglana (lgl)) return 20;
  }
}

static int lglsolve (LGL * lgl) {
  assert (lgl->state == READY);
  if (lgl->mt) return 20;
  assert (!lgl->level && !lgl->failed);
  if (!lglbcptop (lgl)) return 20;
  lglgc (lgl);
  if (lgl->mt) return 20;
  if (lglterminate (lgl)) return 0;
  if (!lglsimp (lgl)) return 20;
  if (lglfailed (lgl)) return 20;
  if (lglterminate (lgl)) return 0;
  lglbias (lgl);
  if (lglterminate (lgl)) return 0;
  lglcutwidth (lgl);
  lglrep (lgl, 1, 's');
  return lglcdcl (lgl);
}

static void lglsetup (LGL * lgl) {
  if (lgl->state == RESET) goto DONE;
  assert (lgl->state == UNUSED || lgl->state == OPTSET || lgl->state == USED);

  lgl->limits.dfg.pshwchs = lgl->stats.pshwchs + lgl->opts.defragint.val;
  lgl->limits.reduce = lgl->opts.redlinit.val;

  lgl->limits.dcp.confs = -1;
  lgl->limits.dcp.visits = -1;
  lgl->limits.dcp.prgss = -1;

  lgl->limits.dst.confs = -1;
  lgl->limits.dst.visits = -1;
  lgl->limits.dst.prgss = -1;

  lgl->limits.elm.confs = -1;
  lgl->limits.elm.visits = -1;
  lgl->limits.elm.prgss = -1;

  lgl->limits.gc.confs = -1;
  lgl->limits.gc.visits = -1;

  lgl->limits.lft.confs = -1;
  lgl->limits.lft.visits = -1;
  lgl->limits.lft.prgss = -1;

  lgl->limits.part.confs = -1;
  lgl->limits.part.visits = -1;

  lgl->limits.prb.confs = -1;
  lgl->limits.prb.visits = -1;
  lgl->limits.prb.prgss = -1;

  lgl->limits.trd.confs = -1;
  lgl->limits.trd.visits = -1;
  lgl->limits.trd.prgss = -1;

  lgl->limits.unhd.confs = -1;
  lgl->limits.unhd.visits = -1;
  lgl->limits.unhd.prgss = -1;

  lgl->limits.term.steps = -1;

  lgl->limits.hla = lgl->opts.hlaminlim.val;

  lgl->limits.rephrase = lgl->opts.rphrint.val;

  lglincrestartl (lgl, 0);
  lglincrebiasl (lgl, 0);

  lgl->rng.w = (unsigned) lgl->opts.seed.val;
  lgl->rng.z = ~lgl->rng.w;
  lgl->rng.w <<= 1;
  lgl->rng.z <<= 1;
  lgl->rng.w += 1;
  lgl->rng.z += 1;
  lgl->rng.w *= 2019164533u, lgl->rng.z *= 1000632769u;

  assert (!lgl->stats.decisions);
  lgl->limits.randec += lgl->opts.randecint.val/2;
  lgl->limits.randec += lglrand (lgl) % lgl->opts.randecint.val;

  if (lgl->opts.plain.val) {
    lgl->opts.block.val = 0;
    lgl->opts.decompose.val = 0;
    lgl->opts.distill.val = 0;
    lgl->opts.elim.val = 0;
    lgl->opts.hte.val = 0;
    lgl->opts.lhbr.val = 0;
    lgl->opts.lift.val = 0;
    lgl->opts.otfs.val = 0;
    lgl->opts.partition.val = 0;
    lgl->opts.probe.val = 0;
    lgl->opts.rebias.val = 0;
    lgl->opts.rephrase.val = 0;
    lgl->opts.restart.val = 0;
    lgl->opts.transred.val = 0;
    lgl->opts.unhide.val = 0;
  }
DONE:
  TRANS (READY);
}

static void lglinitsolve (LGL * lgl) {
  if (lgl->state != READY) lglsetup (lgl);
  lglredvars (lgl);
  lglfitstk (lgl, &lgl->irr);
  lglfitstk (lgl, &lgl->dsched);
#ifndef NCHKSOL
  lglfitstk (lgl, &lgl->orig);
#endif
  lglrep (lgl, 1, '*');
}

#ifndef NLGLPICOSAT
static void lglpicosatchksol (LGL * lgl) {
#ifndef NDEBUG
  int idx, lit, res;
  Val val;
  if (lgl->tid >= 0 || !lgl->opts.check.val) return;
  if (lgl->picosat.res) assert (lgl->picosat.res == 10);
  lglpicosatinit (lgl);
  assert (!picosat_inconsistent ());
  for (idx = 2; idx < lgl->nvars; idx++) {
    val = lglval (lgl, idx);
    assert (val);
    lit = lglsgn (val) * idx;
    picosat_assume (lit);
  }
  if (lgl->assume) picosat_assume (lgl->assume);
  res = picosat_sat (-1);
  assert (res == 10);
  LOG (1, "PicoSAT checked solution");
#endif
}
#endif

static void lgleassign (LGL * lgl, int lit) {
  Ext * ext = lglelit2ext (lgl, lit);
  int pos;
  LOG (3, "%sing external assign %d", ext->repr ? "flipp" : "extend", lit);
  ext->val = lglsgn (lit);
  if ((pos = ext->etrailpos) >= 0) {
    assert (abs (lgl->etrail.start[pos]) == abs (lit));
    lgl->etrail.start[pos] = lit;
  } else {
    ext->etrailpos = lglcntstk (&lgl->etrail);
    lglpushstk (lgl, &lgl->etrail, lit);
  }
}

static void lgleunassign (LGL * lgl, int lit) {
  Ext * ext = lglelit2ext (lgl, lit);
  assert (ext->val == lglsgn (lit));
  LOG (3, "external unassign %d", lit);
  assert (ext->etrailpos >= 0);
  ext->etrailpos = -1;
  ext->val = 0;
}

static void lglextend (LGL * lgl) {
  int * p, lit, next, satisfied, val, * start = lgl->extend.start;
  assert (lgl->state & SATISFIED);
  assert (!(lgl->state & EXTENDED));
  while (!lglmtstk (&lgl->etrail))
    lgleunassign (lgl, lglpopstk (&lgl->etrail));
  p = lgl->extend.top;
  while (p > start) {
    satisfied = 0;
    next = 0;
    do {
      lit = next;
      next = *--p;
      if (!lit || satisfied) continue;
      val = lglideref (lgl, lit);
      assert (!next || val);
      if (val > 0) satisfied = 1;
    } while (next);
    assert (lit);
    if (satisfied) continue;
    lgleassign (lgl, lit);
  }
  TRANS (EXTENDED);
}

#ifndef NCHKSOL
#include <signal.h>
#include <unistd.h>
static void lglchksol (LGL * lgl) {
  int * p, * c, * eoo = lgl->orig.top, lit, satisfied;
  assert (lglmtstk (&lgl->orig) || !eoo[-1]);
  assert (lgl->state == SATISFIED);
  lglextend (lgl);
  for (c = lgl->orig.start; c < eoo; c = p + 1) {
    satisfied = 0;
    for (p = c; (lit = *p); p++)
      if (!satisfied && lglideref (lgl, lit) > 0)
	satisfied = 1;
    if (satisfied) continue;
    fflush (stderr);
    lglmsgstart (lgl, 0);
    printf ("unsatisfied original external clause");
    for (p = c; (lit = *p); p++) printf (" %d", lit);
    lglmsgend (lgl);
    assert (satisfied);
    sleep (1);
    abort ();	// NOTE: not 'lglabort' on purpose !!
  }
}
#endif

int lglsat (LGL * lgl) {
  int res;
  TRAPI ("sat");
  lgl->stats.calls.sat++;
  ABORTIF (!lgl, "can not check satisfiability with uninitialized manager");
  ABORTIF (!lglmtstk (&lgl->clause), "clause terminating zero missing");
  if (lgl->state & (SATISFIED | UNSATISFIED | EXTENDED)) lglreset (lgl);
  lglinitsolve (lgl);
  res = lglsolve (lgl);
  if (!res) TRANS (UNKNOWN);
  if (res == 10) {
    TRANS (SATISFIED);
    lglrep (lgl, 1, '1');
  }
  if (res == 20) {
    TRANS (UNSATISFIED);
    if (!lgl->level && !lgl->mt) assert (lgl->failed);
    lglrep (lgl, 1, '0');
  }
  lglflshrep (lgl);
#ifndef NCHKSOL
  if (res == 10) lglchksol (lgl);
#endif
#ifndef NLGLPICOSAT
  if (res == 10) lglpicosatchksol (lgl);
  if (res == 20) lglpicosatchkunsat (lgl);
#endif
  TRAPI ("return %d", res);
  return res;
}

int lglmaxvar (LGL * lgl) {
  ABORTIF (!lgl, "uninitialized manager");
  return lgl->maxext;
}

int lglderef (LGL * lgl, int elit) {
  int res;
  TRAPI ("deref %d", elit);
  lgl->stats.calls.deref++;
  REQUIRE (SATISFIED | EXTENDED);
  if (!(lgl->state & EXTENDED)) lglextend (lgl);
  res = lglideref (lgl, elit);
  TRAPI ("return %d", res);
  return res;
}

void lglfreeze (LGL * lgl, int elit) {
  Ext * ext;
  TRAPI ("freeze %d", elit);
  lgl->stats.calls.freeze++;
  REQUIRE (UNUSED | OPTSET | USED | RESET | SATISFIED | EXTENDED);
  LOG (2, "freezing external literal %d", elit);
  (void) lglimport (lgl, elit);
  ext = lglelit2ext (lgl, elit);
  ABORTIF (ext->melted, "freezing melted literal %d", elit);
  assert (!ext->blocking && !ext->eliminated);
  ABORTIF (ext->frozen == INT_MAX, "literal %d frozen too often", elit);
  ext->frozen++;
  lglmelter (lgl);
}

void lglmelt (LGL * lgl, int elit) {
  Ext * ext;
  TRAPI ("melt %d", elit);
  lgl->stats.calls.melt++;
  REQUIRE (OPTSET | USED | RESET | SATISFIED | EXTENDED);
  LOG (2, "melting external literal %d", elit);
  (void) lglimport (lgl, elit);
  ext = lglelit2ext (lgl, elit);
  ABORTIF (!ext->frozen, "can not melt fully unfrozen literal %d", elit);
  assert (!ext->blocking && !ext->eliminated);
  ext->frozen--;
  lglmelter (lgl);
}

static void lglprs (LGL * lgl, const char * fmt, ...) {
  va_list ap;
  assert (lgl->stats.prefix && lgl->stats.file);
  fputs (lgl->stats.prefix, lgl->stats.file);
  if (lgl->tid >= 0) fprintf (lgl->stats.file, "%d ", lgl->tid);
  va_start (ap, fmt);
  vfprintf (lgl->stats.file, fmt, ap);
  va_end (ap);
  fputc ('\n', lgl->stats.file);
}

static double lglsqr (double a) { return a*a; }

static void lglgluestats (LGL * lgl) {
  int64_t added, reduced, forcing, resolved, conflicts;
  int64_t wadded, wreduced, wforcing, wresolved, wconflicts;
  int64_t avgadded, avgreduced, avgforcing, avgresolved, avgconflicts;
  double madded, mreduced, mforcing, mresolved, mconflicts;
  double vadded, vreduced, vforcing, vresolved, vconflicts;
  double sadded, sreduced, sforcing, sresolved, sconflicts;
  int count, glue;
  Lir * lir;
  lglprs (lgl, "");
  lglprs (lgl, "scaledglue%7s %3s %9s %3s %9s %3s %9s %3s %9s",
	  "added","",
	  "reduced","",
	  "forcing","",
	  "resolved","",
	  "conflicts");
  count = 0;
  added = reduced = forcing = resolved = conflicts = 0;
  wadded = wreduced = wforcing = wresolved = wconflicts = 0;
  for (glue = 0; glue <= MAXGLUE; glue++) {
    lir = lgl->red + glue;
    added += lgl->stats.lir[glue].added;
    reduced += lgl->stats.lir[glue].reduced;
    forcing += lgl->stats.lir[glue].forcing;
    resolved += lgl->stats.lir[glue].resolved;
    conflicts += lgl->stats.lir[glue].conflicts;
    wadded += glue*lgl->stats.lir[glue].added;
    wreduced += glue*lgl->stats.lir[glue].reduced;
    wforcing += glue*lgl->stats.lir[glue].forcing;
    wresolved += glue*lgl->stats.lir[glue].resolved;
    wconflicts += glue*lgl->stats.lir[glue].conflicts;
  }
  avgadded = added ? (((10*wadded)/added+5)/10) : 0;
  avgreduced = reduced ? (((10*wreduced)/reduced+5)/10) : 0;
  avgforcing = forcing ? (((10*wforcing)/forcing+5)/10) : 0;
  avgresolved = resolved ? (((10*wresolved)/resolved+5)/10) : 0;
  avgconflicts = conflicts ? (((10*wconflicts)/conflicts+5)/10) : 0;
  lglprs (lgl, "");
  lglprs (lgl,
    "all %9lld %3.0f %9lld %3.0f %9lld %3.0f %9lld %3.0f %9lld %3.0f",
     (long long) added, 100.0,
     (long long) reduced, 100.0,
     (long long) forcing, 100.0,
     (long long) resolved, 100.0,
     (long long) conflicts, 100.0);
  lglprs (lgl, "");
  for (glue = 0; glue <= MAXGLUE; glue++) {
    lir = lgl->red + glue;
    lglprs (lgl,
"%2d  %9lld %3.0f%c%9lld %3.0f%c%9lld %3.0f%c%9lld %3.0f%c%9lld %3.0f%c",
      glue,
      (long long) lgl->stats.lir[glue].added,
	lglpcnt (lgl->stats.lir[glue].added, added),
	(glue == avgadded) ? '<' : ' ',
      (long long) lgl->stats.lir[glue].reduced,
	lglpcnt (lgl->stats.lir[glue].reduced, reduced),
	(glue == avgreduced) ? '<' : ' ',
      (long long) lgl->stats.lir[glue].forcing,
	lglpcnt (lgl->stats.lir[glue].forcing, forcing),
	(glue == avgforcing) ? '<' : ' ',
      (long long) lgl->stats.lir[glue].resolved,
	lglpcnt (lgl->stats.lir[glue].resolved, resolved),
	(glue == avgresolved) ? '<' : ' ',
      (long long) lgl->stats.lir[glue].conflicts,
	lglpcnt (lgl->stats.lir[glue].conflicts, conflicts),
	(glue == avgconflicts) ? '<' : ' ');
  }
  lglprs (lgl, "");

  madded = lglavg (wadded, added),
  mreduced = lglavg (wreduced, reduced),
  mforcing = lglavg (wforcing, forcing),
  mresolved = lglavg (wresolved, resolved),
  mconflicts = lglavg (wconflicts, conflicts);

  lglprs (lgl,
    "avg  %14.1f%14.1f%14.1f%14.1f%14.1f",
     madded, mreduced, mforcing, mresolved, mconflicts);

  vadded = vreduced = vforcing = vresolved = vconflicts = 0;
  for (glue = 0; glue <= MAXGLUE; glue++) {
    lir = lgl->red + glue;
    vadded += lgl->stats.lir[glue].added * lglsqr (glue - madded);
    vreduced += lgl->stats.lir[glue].reduced * lglsqr (glue - mreduced);
    vforcing += lgl->stats.lir[glue].forcing * lglsqr (glue - mforcing);
    vresolved += lgl->stats.lir[glue].resolved * lglsqr (glue - mresolved);
    vconflicts += lgl->stats.lir[glue].conflicts * lglsqr (glue - mconflicts);
  }
  sadded = sqrt (lglavg (vadded, added));
  sreduced = sqrt (lglavg (vreduced, reduced));
  sforcing = sqrt (lglavg (vforcing, forcing));
  sresolved = sqrt (lglavg (vresolved, resolved));
  sconflicts = sqrt (lglavg (vconflicts, conflicts));

  lglprs (lgl,
    "std  %14.1f%14.1f%14.1f%14.1f%14.1f",
     sadded, sreduced, sforcing, sresolved, sconflicts);
}

void lglstats (LGL * lgl, const char * prefix, FILE * file) {
  double t = lglsec (lgl), r;
  Stats * s = &lgl->stats;
  int64_t p = s->props.search + s->props.simp;
  int64_t v = s->visits.search + s->visits.simp;
  struct { int taut, rem; } all, red, irr;
  struct { int trn, lrg; } taut, rem;
  int remaining, removed, sum;
  int64_t min;
  ABORTIF (!lgl, "can not print statistics of uninitialized manager");
  lgl->stats.prefix = prefix;
  lgl->stats.file = file;
  lglprs (lgl, "blkd: %d blocked clauses in %lld resolutions",
          s->blk.clauses, (long long) s->blk.res);
  lglprs (lgl, "blkd: %d blocking literals %.0f%%",
          s->blk.lits, lglpcnt (s->blk.lits, 2*lgl->maxext));
  lglprs (lgl, "clls: %lld sat, %lld freeze, %lld melt",
          (long long) s->calls.sat,
          (long long) s->calls.freeze,
          (long long) s->calls.melt);
  lglprs (lgl, "clls: %lld add, %lld assume, %lld deref",
          (long long) s->calls.add,
          (long long) s->calls.assume,
          (long long) s->calls.deref);
  lglprs (lgl, "coll: %d gcs, %d rescored vars, %d rescored clauses",
	  s->gcs, s->rescored.vars, s->rescored.clauses);
  lglprs (lgl, "dcps: %d decompositions, %d equivalent %.0f%%",
          s->decomps, s->equiv.sum, lglpcnt (s->equiv.sum, lgl->maxext));
  lglprs (lgl, "decs: %lld decisions, %lld random %.3f%%",
          (long long) s->decisions, (long long) s->randecs,
	  lglpcnt (s->randecs, s->decisions));
  lglprs (lgl,
          "dsts: %d distillations, %d redundant, %d failed, %d strengthened",
	  s->dst.count, s->dst.red, s->dst.failed, s->dst.str);
  lglprs (lgl, "elms: %d elims, %d rounds, %d skipped, %d eliminated %.0f%%",
          s->elm.count, s->elm.rounds, s->elm.skipped,
	  s->elm.elmd, lglpcnt (s->elm.elmd, lgl->maxext));
  lglprs (lgl, "elms: %d small %.0f%%, %d forced %.0f%%,  %d large %.0f%%",
          s->elm.small.elm, lglpcnt (s->elm.small.elm, s->elm.elmd),
          s->elm.forced, lglpcnt (s->elm.forced, s->elm.elmd),
          s->elm.large, lglpcnt (s->elm.large, s->elm.elmd));
  lglprs (lgl, "elms: %d tried small, %d succeeded %.0f%%, %d failed %.0f%%",
	  s->elm.small.tried,
	  s->elm.small.tried - s->elm.small.failed,
	    lglpcnt (s->elm.small.tried - s->elm.small.failed,
	             s->elm.small.tried),
	  s->elm.small.failed,
	    lglpcnt (s->elm.small.failed, s->elm.small.tried));
  lglprs (lgl, "elms: %d subsumed, %d strengthened, %d blocked",
          s->elm.sub, s->elm.str, s->elm.blkd);
  lglprs (lgl, "elms: %lld copies, %lld resolutions, %d htes",
          (long long) s->elm.copies, (long long) s->elm.resolutions,
	  s->elm.htes);
  lglprs (lgl, "elms: %lld subchks, %lld strchks",
          (long long) s->elm.subchks, (long long) s->elm.strchks);
  lglprs (lgl, "glue: %.1f avg, %.1f scaled avg, %d capped",
          lglavg (s->clauses.glue, s->clauses.learned),
          lglavg (s->clauses.scglue, s->clauses.learned),
          s->clauses.capped);
  lglprs (lgl, "glue: %lld maxredglue=%d (%.0f%%), %lld kept (%.0f%%)",
	  s->clauses.maxglue, MAXGLUE,
          lglpcnt (s->clauses.maxglue, s->clauses.learned),
	  s->clauses.keptmaxglue,
          lglpcnt (s->clauses.keptmaxglue, s->clauses.maxglue));
  sum = s->lift.probed[0] + s->lift.probed[1];
  lglprs (lgl, "lift: %d phases, "
          "%d probed (%lld level1 %.0f%%, %lld level2 %.0f%%)",
          s->lift.count, sum,
	  s->lift.probed[0], lglpcnt (s->lift.probed[0], sum),
	  s->lift.probed[1], lglpcnt (s->lift.probed[1], sum));
  lglprs (lgl,
          "lift: %d units, %d equivalences, %d implications",
	  s->lift.units, s->lift.eqs, s->lift.impls);
  lglprs (lgl,
          "hbrs: %d static = %d trn %.0f%% + %d lrg %.0f%%, %d sub %.0f%%",
          s->hbr.cnt,
	  s->hbr.trn, lglpcnt (s->hbr.trn, s->hbr.cnt),
	  s->hbr.lrg, lglpcnt (s->hbr.lrg, s->hbr.cnt),
	  s->hbr.sub, lglpcnt (s->hbr.sub, s->hbr.cnt));
  red.taut = s->hte.taut.red.lrg + s->hte.taut.red.trn;
  red.rem = s->hte.rem.red.lrg + s->hte.rem.red.trn;
  irr.taut = s->hte.taut.irr.lrg + s->hte.taut.irr.trn;
  irr.rem = s->hte.rem.irr.lrg + s->hte.rem.irr.trn;
  taut.lrg = s->hte.taut.red.lrg + s->hte.taut.irr.lrg;
  taut.trn = s->hte.taut.red.trn + s->hte.taut.irr.trn;
  rem.lrg = s->hte.rem.red.lrg + s->hte.rem.irr.lrg;
  rem.trn = s->hte.rem.red.trn + s->hte.rem.irr.trn;
  all.taut = red.taut + irr.taut;
  all.rem = red.rem + irr.rem;
  lglprs (lgl, "htes: %d htes, %lld steps (%.0f%% hla, %.0f%% cls), %d failed",
	  s->hte.count,
	  (long long) s->hte.all.steps,
	  lglpcnt (s->hte.hla.steps, s->hte.all.steps),
	  lglpcnt (s->hte.cls.steps, s->hte.all.steps),
	  s->hte.failed);
  lglprs (lgl,
          "htes: all: %d taut (%0.f%% trn), %d rem (%.0f%% trn)",
          all.taut, lglpcnt (taut.trn, all.taut),
          all.rem, lglpcnt (rem.trn, all.rem));
  lglprs (lgl, "htes: irr: %d taut (%0.f%% trn), %d rem (%.0f%% trn)",
          irr.taut, lglpcnt (s->hte.taut.irr.trn, irr.taut),
          irr.rem, lglpcnt (s->hte.rem.irr.trn, irr.rem));
  lglprs (lgl, "htes: red: %d taut (%0.f%% trn), %d rem (%.0f%% trn)",
          red.taut, lglpcnt (s->hte.taut.red.trn, red.taut),
          red.rem, lglpcnt (s->hte.rem.red.trn, red.rem));
  lglprs (lgl, "lrnd: %lld clauses, %lld uips %.0f%%, %.1f length, %.1f glue",
          s->clauses.learned,
	  s->uips, lglpcnt (s->uips, s->clauses.learned),
          lglavg (s->lits.learned, s->clauses.learned),
          lglavg (s->clauses.glue, s->clauses.learned));
  min = s->lits.nonmin - s->lits.learned;
  lglprs (lgl, "mins: %lld learned lits, %.0f%% minimized",
          (long long) s->lits.learned, lglpcnt (min, s->lits.nonmin));
  assert (s->lits.nonmin >= s->lits.learned);
  lglprs (lgl, "otfs: str %d dyn (%d red, %d irr)",
          s->otfs.str.dyn.red + s->otfs.str.dyn.irr,
          s->otfs.str.dyn.red, s->otfs.str.dyn.irr);
  lglprs (lgl, "otfs: sub %d dyn (%d red, %d irr), %d drv",
          s->otfs.sub.dyn.red + s->otfs.sub.dyn.irr,
          s->otfs.sub.dyn.red, s->otfs.sub.dyn.irr,
	  s->otfs.driving);
  lglprs (lgl, "part: %d cnt, %d max, %.1f average",
          s->part.count, s->part.max, lglavg (s->part.sum, s->part.count));
  lglprs (lgl, "prbs: %d cnt, %lld probed, %d failed, %d lifted",
          s->prb.count, (long long) s->prb.probed,
	  s->prb.failed, s->prb.lifted);
  lglprs (lgl, "prps: %lld props, %.0f%% srch, %.0f%% simp, %.0f props/dec",
          (long long) p, lglpcnt (s->props.search, p),
	  lglpcnt (s->props.simp, p), lglavg (s->props.search, s->decisions));
  lglprs (lgl, "psns: %lld searches, %lld hits, %.0f%% hit rate",
          (long long) s->poison.search, (long long) s->poison.hits,
	  lglpcnt (s->poison.hits, s->poison.search));
  sum = s->rebias.count + s->rebias.skipped;
  lglprs (lgl, "rebs: %d rebiased %.0f%%, %d skipped %.0f%%",
          s->rebias.count, lglpcnt (s->rebias.count, sum),
          s->rebias.skipped, lglpcnt (s->rebias.skipped, sum));
  lglprs (lgl, "reds: %d reductions, %d acts %.0f%%, %d exp %.0f%%",
          s->reduced.count, 
	  s->acts, lglpcnt (s->acts, s->reduced.count),
          s->reduced.geom, lglpcnt (s->reduced.geom, s->reduced.count));
  lglprs (lgl, "rmbd: %d removed, %d red %.0f%%",
          s->bindup.removed, s->bindup.red,
	  lglpcnt (s->bindup.red, s->bindup.removed));
  lglprs (lgl, "rphr: %d rephrased", s->rephrased);
  sum = s->restarts.count + s->restarts.skipped;
  lglprs (lgl, "rsts: %d restarts %.0f%%, %d skipped %.0f%%",
          s->restarts.count, lglpcnt (s->restarts.count, sum),
          s->restarts.skipped, lglpcnt (s->restarts.skipped, sum));
  lglprs (lgl, "rsts: %d kept %.1f%% average %.1f%%",
	  s->restarts.kept.count,
	  lglpcnt (s->restarts.kept.count, s->restarts.count),
	  100.0 * lglavg (s->restarts.kept.sum, s->restarts.kept.count));
  lglprs (lgl, "tops: %d fixed %.0f%%, %d iterations",
          s->fixed.sum, lglpcnt (s->fixed.sum, lgl->maxext), s->iterations);
  lglprs (lgl, "trds: %d transitive reductions, %d removed, %d failed",
	  s->trd.count, s->trd.red, s->trd.failed);
  lglprs (lgl, "trds: %lld nodes, %lld edges, %lld steps",
          (long long) s->trd.lits, (long long) s->trd.bins,
	  (long long) s->trd.steps);
  lglprs (lgl, "unhd: %d count, %d rounds, %lld steps",
          s->unhd.count, s->unhd.rounds, (long long) s->unhd.steps);
  lglprs (lgl, "unhd: %d non-trivial sccs of average size %.1f",
          s->unhd.stamp.sccs,
          lglavg (s->unhd.stamp.sumsccsizes, s->unhd.stamp.sccs));
  sum = lglunhdunits (lgl);
  lglprs (lgl, "unhd: %d units, %d bin, %d trn, %d lrg",
	  sum, s->unhd.units.bin, s->unhd.units.trn, s->unhd.units.lrg);
  sum = lglunhdfailed (lgl);
  lglprs (lgl, "unhd: %d failed, %d stamp, %d lits, %d bin, %d trn, %d lrg",
	  sum, s->unhd.stamp.failed, s->unhd.failed.lits,
	  s->unhd.failed.bin, s->unhd.failed.trn, s->unhd.units.lrg);
  sum = lglunhdtauts (lgl);
  lglprs (lgl,
          "unhd: %d tauts, %d bin %.0f%%, %d trn %.0f%%, %d lrg %.0f%%",
          sum,
	  s->unhd.tauts.bin, lglpcnt (s->unhd.tauts.bin, sum),
	  s->unhd.tauts.trn, lglpcnt (s->unhd.tauts.trn, sum),
	  s->unhd.tauts.lrg, lglpcnt (s->unhd.tauts.lrg, sum));
  lglprs (lgl,
          "unhd: %d tauts, %d stamp %.0f%%, %d red %.0f%%",
          sum,
	  s->unhd.stamp.trds, lglpcnt (s->unhd.stamp.trds, sum),
	  s->unhd.tauts.red, lglpcnt (s->unhd.tauts.red, sum));
  sum = lglunhdhbrs (lgl);
  lglprs (lgl,
          "unhd: %d hbrs, %d trn %.0f%%, %d lrg %.0f%%, %d red %.0f%%",
          sum,
	  s->unhd.hbrs.trn, lglpcnt (s->unhd.hbrs.trn, sum),
	  s->unhd.hbrs.lrg, lglpcnt (s->unhd.hbrs.lrg, sum),
	  s->unhd.hbrs.red, lglpcnt (s->unhd.hbrs.red, sum));
  sum = lglunhdstrd (lgl);
  lglprs (lgl,
          "unhd: %d strd, %d bin %.0f%%, %d trn %.0f%%, "
	  "%d lrg %.0f%%, %d red %.0f%%",
          sum,
	  s->unhd.units.bin, lglpcnt (s->unhd.units.bin, sum),
	  s->unhd.str.trn, lglpcnt (s->unhd.str.trn, sum),
	  s->unhd.str.lrg, lglpcnt (s->unhd.str.lrg, sum),
	  s->unhd.str.red, lglpcnt (s->unhd.str.red, sum));
  removed = s->fixed.sum + s->elm.elmd + s->equiv.sum;
  remaining = lgl->maxext - removed;
  assert (remaining >= 0);
  lglprs (lgl, "vars: %d remaining %.0f%% and %d removed %.0f%% out of %d",
          remaining, lglpcnt (remaining, lgl->maxext),
          removed, lglpcnt (removed, lgl->maxext),
	  lgl->maxext);
  lglprs (lgl, "vars: %d fixed %.0f%%, "
                     "%d eliminated %.0f%%, "
                     "%d equivalent %.0f%%",
	  s->fixed.sum, lglpcnt (s->fixed.sum, lgl->maxext),
	  s->elm.elmd, lglpcnt (s->elm.elmd, lgl->maxext),
	  s->equiv.sum, lglpcnt (s->equiv.sum, lgl->maxext));
  lglprs (lgl, "vsts: %lld visits, %.0f%% srch, %.0f%% simp, %.1f visits/prop",
          (long long) v, lglpcnt (s->visits.search, v),
	  lglpcnt (s->visits.simp, v), lglavg (v, p));
  lglprs (lgl, "wchs: %lld pushed, %lld enlarged, %d defrags",
           (long long) s->pshwchs, (long long) s->enlwchs, s->defrags);
  lglgluestats (lgl);
  lglprs (lgl, "");
  lglprs (lgl, "%lld decisions, %lld conflicts, %.1f conflicts/sec",
          (long long) s->decisions, (long long) s->confs,
	  lglavg (s->confs, t));
  lglprs (lgl, "%lld propagations, %.1f megaprops/sec",
          (long long) p, lglavg (p/1e6, t));
  lglprs (lgl, "%.1f seconds, %.1f MB", t, lglmaxmb (lgl));
  lglprs (lgl, "");
  r = t;
  r -= s->tms.elm;
  lglprs (lgl, "%8.3f %3.0f%% elim", s->tms.elm, lglpcnt (s->tms.elm, t));
  r -= s->tms.dcp;
  lglprs (lgl, "%8.3f %3.0f%% decomp", s->tms.dcp, lglpcnt (s->tms.dcp, t));
  r -= s->tms.dfg;
  lglprs (lgl, "%8.3f %3.0f%% defrag", s->tms.dfg , lglpcnt (s->tms.dfg , t));
  r -= s->tms.dst;
  lglprs (lgl, "%8.3f %3.0f%% distill", s->tms.dst, lglpcnt (s->tms.dst, t));
  r -= s->tms.gc;
  lglprs (lgl, "%8.3f %3.0f%% gc", s->tms.gc, lglpcnt (s->tms.gc, t));
  r -= s->tms.lft;
  lglprs (lgl, "%8.3f %3.0f%% lift", s->tms.lft, lglpcnt (s->tms.lft, t));
  r -= s->tms.part;
  lglprs (lgl, "%8.3f %3.0f%% part", s->tms.part, lglpcnt (s->tms.part, t));
  r -= s->tms.prb;
  lglprs (lgl, "%8.3f %3.0f%% probe", s->tms.prb, lglpcnt (s->tms.prb, t));
  r -= s->tms.red;
  lglprs (lgl, "%8.3f %3.0f%% reduce", s->tms.red , lglpcnt (s->tms.red , t));
  r -= s->tms.trd;
  lglprs (lgl, "%8.3f %3.0f%% transred", s->tms.trd, lglpcnt (s->tms.trd, t));
  r -= s->tms.unhd;
  lglprs (lgl, "%8.3f %3.0f%% unhide", s->tms.unhd, lglpcnt (s->tms.unhd, t));
  lglprs (lgl, "-----------------------");
  lglprs (lgl, "%8.3f %3.0f%% analysis", s->tms.ana, lglpcnt (s->tms.ana, t));
  lglprs (lgl, "%8.3f %3.0f%% block", s->tms.blk , lglpcnt (s->tms.blk , t));
  lglprs (lgl, "%8.3f %3.0f%% block gc", s->tms.gcb, lglpcnt (s->tms.gcb, t));
  lglprs (lgl, "%8.3f %3.0f%% decomp trj", s->tms.trj, lglpcnt (s->tms.trj, t));
  lglprs (lgl, "%8.3f %3.0f%% decomp gc", s->tms.gcd, lglpcnt (s->tms.gcd, t));
  lglprs (lgl, "%8.3f %3.0f%% elim gc", s->tms.gce, lglpcnt (s->tms.gce, t));
  lglprs (lgl, "%8.3f %3.0f%% hte", s->tms.hte , lglpcnt (s->tms.hte , t));
  lglprs (lgl, "%8.3f %3.0f%% rebias", s->tms.reb, lglpcnt (s->tms.reb, t));
  lglprs (lgl, "%8.3f %3.0f%% restart", s->tms.rsts, lglpcnt (s->tms.rsts, t));
  lglprs (lgl, "%8.3f %3.0f%% unhide gc", s->tms.gcu, lglpcnt (s->tms.gcu, t));
  lglprs (lgl, "-----------------------");
  lglprs (lgl, "%8.3f %3.0f%% simplifying", t - r, lglpcnt (t - r, t));
  lglprs (lgl, "%8.3f %3.0f%% search", r, lglpcnt (r, t));
  lglprs (lgl, "=======================");
  lglprs (lgl, "%8.3f %3.0f%% all", t, 100.0);
  fflush (lgl->stats.file);
}

int64_t lglgetprops (LGL * lgl) {
  ABORTIF (!lgl, "uninitialized manager");
  return lgl->stats.props.search + lgl->stats.props.simp;
}

int64_t lglgetconfs (LGL * lgl) {
  ABORTIF (!lgl, "uninitialized manager");
  return lgl->stats.confs;
}

int64_t lglgetdecs (LGL * lgl) {
  ABORTIF (!lgl, "uninitialized manager");
  return lgl->stats.decisions;
}

void lglsizes (void) {
  printf ("c sizeof (int) == %ld\n", (long) sizeof (int));
  printf ("c sizeof (unsigned) == %ld\n", (long) sizeof (unsigned));
  printf ("c sizeof (void*) == %ld\n", (long) sizeof (void*));
  printf ("c sizeof (Stk) == %ld\n", (long) sizeof (Stk));
  printf ("c sizeof (AVar) == %ld\n", (long) sizeof (AVar));
  printf ("c sizeof (DVar) == %ld\n", (long) sizeof (DVar));
  printf ("c sizeof (EVar) == %ld\n", (long) sizeof (EVar));
  printf ("c sizeof (LGL) == %ld\n", (long) sizeof (LGL));
  printf ("c MAXVAR == %ld\n", (long) MAXVAR);
  printf ("c MAXREDLIDX == %ld\n", (long) MAXREDLIDX);
  printf ("c MAXIRRLIDX == %ld\n", (long) MAXIRRLIDX);
  fflush (stdout);
}

void lglrelease (LGL * lgl) {
  int i;
  TRAPI ("release");
  ABORTIF (!lgl, "can not release uninitialized manager");
  DEL (lgl->avars, lgl->szvars);
  DEL (lgl->dvars, lgl->szvars);
  DEL (lgl->vals, lgl->szvars);
  DEL (lgl->i2e, lgl->szvars);
  DEL (lgl->ext, lgl->szext);
  DEL (lgl->df.pos.dfs, lgl->df.pos.szdfs);
  DEL (lgl->df.neg.dfs, lgl->df.neg.szdfs);
  lglrelstk (lgl, &lgl->wchs);
  lglrelstk (lgl, &lgl->resolvent);
  lglrelstk (lgl, &lgl->extend);
  lglrelstk (lgl, &lgl->clause);
  lglrelstk (lgl, &lgl->dsched);
  lglrelstk (lgl, &lgl->irr);
  for (i = 0; i <= MAXGLUE; i++)
    lglrelstk (lgl, &lgl->red[i].lits);
  lglrelstk (lgl, &lgl->trail);
  lglrelstk (lgl, &lgl->etrail);
  lglrelctk (lgl, &lgl->control);
  lglrelstk (lgl, &lgl->frames);
  lglrelstk (lgl, &lgl->saved);
  lglrelstk (lgl, &lgl->seen);
  lglrelstk (lgl, &lgl->poisoned);
  lglrelstk (lgl, &lgl->sortstk);
  DEL (lgl->drail, lgl->szdrail);
#ifndef NDEBUG
#ifndef NLGLPICOSAT
  if (lgl->tid < 0 && lgl->picosat.init) {
    if (lgl->opts.verbose.val > 0 && lgl->opts.check.val > 0) picosat_stats ();
    picosat_reset ();
  }
#endif
#endif
#ifndef NCHKSOL
  lglrelstk (lgl, &lgl->orig);
#endif
  assert (getenv ("LGLEAK") || !lgl->stats.bytes.current);
  if (lgl->closeapitrace == 1) fclose (lgl->apitrace);
  if (lgl->closeapitrace == 2) pclose (lgl->apitrace);
  free (lgl);
}

#ifndef NDEBUG

void lgldump (LGL * lgl) {
  int idx, sign, lit, blit, tag, red, other, other2, glue;
  const int * p, * w, * eow, * c, * start;
  Lir * lir;
  HTS * hts;
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = lglhts (lgl, lit);
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	red = blit & REDCS;
	if (tag == TRNCS || tag == LRGCS) p++;
        if (tag == BINCS) {
	  other = blit >> RMSHFT;
	  if (abs (other) < idx) continue;
	  other2 = 0;
	} else if (tag == TRNCS) {
	  other = blit >> RMSHFT;
	  if (abs (other) < idx) continue;
	  other2 = *p;
	  if (abs (other2) < idx) continue;
	} else continue;
	printf ("%s %d %d", red ? "red" : "irr", lit, other);
	if (tag == TRNCS) printf (" %d", other2);
	printf ("\n");
      }
    }
  for (c = lgl->irr.start; c < lgl->irr.top; c = p + 1) {
    p = c;
    if (*p >= NOTALIT) continue;
    printf ("irr");
    while (*p) printf (" %d", *p++);
    printf ("\n");
  }
  for (glue = 0; glue < MAXGLUE; glue++) {
    lir = lgl->red + glue;
    start = lir->lits.start;
    for (c = start; c < lir->lits.top; c = p + 1) {
      p = c;
      if (*p >= NOTALIT) continue;
      printf ("glue%d", glue);
      while (*p) printf (" %d", *p++);
    }
  }
}

#endif

#ifndef NLGLPICOSAT
//#warning "PicoSAT checking code included"//TODO FIXME
#endif

#ifndef NCHKSOL
//#warning "solution checking code included"//TODO FIXME
#endif
