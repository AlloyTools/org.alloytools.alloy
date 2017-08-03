/* Copyright 2010-2011 Armin Biere, Johannes Kepler University, Linz, Austria */

#include "lglib.h"

#include <assert.h>
#include <execinfo.h>
#include <ctype.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>
#include <stdarg.h>
#include <signal.h>
#include <unistd.h>

#define NWORKERS 8
#define NUNITS (1<<9)
#define NOEQ 0

#define NEW(PTR,N) \
do { \
  size_t BYTES = (N) * sizeof *(PTR); \
  if (!((PTR) = malloc (BYTES))) die ("out of memory"); \
  allocated += BYTES; \
  assert (allocated >= 0); \
  memset ((PTR), 0, BYTES); \
} while (0)

typedef struct Worker {
  LGL * lgl;
  pthread_t thread;
  int res, fixed;
  int units[NUNITS], nunits;
  struct {
    struct { int calls, produced, consumed; } units;
    struct { int produced, consumed; } eqs;
    int produced, consumed;
  } stats;
} Worker;

static int nworkers;
static Worker * workers;
static int nvars, nclauses;
static int * vals, * fixed, * repr;
static int nfixed, globalres;
static int verbose, plain, ignaddcls, noeq = NOEQ;
#ifndef NLGLOG
static int loglevel;
#endif
static const char * name;
static size_t allocated;
static int catchedsig;
static double start;
static FILE * file;

struct { int units, eqs; } syncs;
static int done, termchks, units, eqs, flushed;
static pthread_mutex_t donemutex = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t msgmutex = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t fixedmutex = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t reprmutex = PTHREAD_MUTEX_INITIALIZER;

static double currentime (void) {
  double res = 0;
  struct timeval tv;
  if (!gettimeofday (&tv, 0)) res = 1e-6 * tv.tv_usec, res += tv.tv_sec;
  return res;
}

static double getime () { return currentime () - start; }

static void msg (int wid, int level, const char * fmt, ...) {
  va_list ap;
  if (verbose < level) return;
  pthread_mutex_lock (&msgmutex);
  if (wid < 0) printf ("c - "); else printf ("c %d ", wid);
  printf ("W %6.1f ", getime ());
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  fputc ('\n', stdout);
  fflush (stdout);
  pthread_mutex_unlock (&msgmutex);
}

static void die (const char * fmt, ...) {
  va_list ap;
  fputs ("*** plingeling error: ", stderr);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  fputc ('\n', stderr);
  fflush (stderr);
  exit (1);
}

static void warn (const char * fmt, ...) {
  va_list ap;
  fputs ("*** plingeling warning: ", stderr);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  fputc ('\n', stderr);
  fflush (stderr);
}

static void (*sig_int_handler)(int);
static void (*sig_segv_handler)(int);
static void (*sig_abrt_handler)(int);
static void (*sig_term_handler)(int);

static void resetsighandlers (void) {
  (void) signal (SIGINT, sig_int_handler);
  (void) signal (SIGSEGV, sig_segv_handler);
  (void) signal (SIGABRT, sig_abrt_handler);
  (void) signal (SIGTERM, sig_term_handler);
}

static void caughtsigmsg (int sig) {
  if (!verbose) return;
  printf ("c\nc CAUGHT SIGNAL %d\nc\n", sig);
  fflush (stdout);
}

static void stats (void) {
  double real, process, mpps, cps, mb;
  int64_t decs, confs, props;
  int i, unitcalls;
  unitcalls = decs = confs = 0;
  props = 0;
  mb = allocated / (double)(1<<20);
  for (i = 0; i < nworkers; i++) {
    decs += lglgetdecs (workers[i].lgl);
    confs += lglgetconfs (workers[i].lgl);
    props += lglgetprops (workers[i].lgl);
    mb += lglmaxmb (workers[i].lgl);
    unitcalls += workers[i].stats.units.calls;
  }
  real = getime ();
  process = lglprocesstime ();
  cps = real > 0 ? confs / real : 0;
  mpps = real > 0 ? (props/1e6) / real : 0;
  printf ("c equiv: %d found, %d syncs\n", eqs, syncs.eqs);
  printf ("c terms: %d termination checks\n", termchks);
  printf ("c units: %d found, %d publications, %d syncs, %d flushed\n", 
          units, unitcalls, syncs.units, flushed);
  printf ("c\n");
  printf ("c %lld decisions, %lld conflicts, %.1f conflicts/sec\n", 
          (long long)decs, (long long)confs, cps);
  printf ("c %lld0 propagations, %.1f megaprops/sec\n",
          (long long)props, mpps);
  printf ("c %.1f process time, %.0f%% utilization\n",
          process, real > 0 ? (100.0 * process) / real / nworkers : 0.0);
  printf ("c\n");
  printf ("c %.1f seconds, %.1f MB\n", real, mb);
  fflush (stdout);
}

static void catchsig (int sig) {
  if (!catchedsig) {
#if 0
    void * a[10];
    size_t s;
    s = backtrace (a, sizeof (sizeof a/sizeof *a));
    fprintf (stderr, "*** plingeling.c: caught signal %d at:\n", sig);
    backtrace_symbols_fd (a, s, 2);
#endif
    catchedsig = 1;
    caughtsigmsg (sig);
    if (verbose) stats (), caughtsigmsg (sig);
  }
  resetsighandlers ();
  if (!getenv ("LGLNABORT")) raise (sig); else exit (1);
}

static void setsighandlers (void) {
  sig_int_handler = signal (SIGINT, catchsig);
  sig_segv_handler = signal (SIGSEGV, catchsig);
  sig_abrt_handler = signal (SIGABRT, catchsig);
  sig_term_handler = signal (SIGTERM, catchsig);
}

static const char * parse (void) {
  int ch, lit, sign, i;
HEADER:
  ch = getc (file);
  if (ch == 'c') {
    while ((ch = getc (file)) != '\n')
      if (ch == EOF) return "EOF in comment";
    goto HEADER;
  }
  if (ch != 'p') return "expected header or comment";
  ungetc (ch, file);
  if (fscanf (file, "p cnf %d %d", &nvars, &nclauses) != 2)
    return "can not parse header";
  msg (-1, 1, "p cnf %d %d", nvars, nclauses);
  NEW (fixed, nvars + 1);
  NEW (vals, nvars + 1);
  if (!noeq) NEW (repr, nvars + 1);
LIT:
  ch = getc (file);
  if (ch == 'c') {
    while ((ch = getc (file)) != '\n')
      if (ch == EOF) return "EOF in comment";
    goto LIT;
  }
  if (ch == ' ' || ch == '\n' || ch == '\r' || ch == '\t') goto LIT;
  if (ch == EOF) {
    if (nclauses > 0) return "not enough clauses";
DONE:
    msg (-1, 1, "finished parsing in %.1f seconds", getime ());
    return 0;
  }
  if (ch == '-') {
    ch = getc (file);
    sign = -1;
  } else sign = 1;
  if (!isdigit (ch)) return "expected digit";
  if (!nclauses) return "too many clauses";
  lit = ch - '0';
  while (isdigit (ch = getc (file)))
    lit = 10 * lit + (ch - '0');
  if (lit < 0 || lit > nvars) return "invalid variable index";
  lit *= sign;
  for (i = 0; i < nworkers; i++)
    lgladd (workers[i].lgl, lit);
  if (!lit) {
    nclauses--;
    if (ignaddcls && !nclauses) goto DONE;
  }
  goto LIT;
}

static int isposnum (const char * str) {
  int ch;
  if (!(ch = *str++) || !isdigit (ch)) return 0;
  while (isdigit (ch = *str++))
    ;
  return !ch;
}

static int term (void * voidptr) {
  Worker * worker = voidptr;
  int wid = worker - workers, res;
  assert (0 <= wid && wid < nworkers);
  msg (wid, 3, "checking early termination");
  if (pthread_mutex_lock (&donemutex))
    warn ("failed to lock 'done' mutex in termination check");
  res = done;
  termchks++;
  if (pthread_mutex_unlock (&donemutex)) 
    warn ("failed to unlock 'done' mutex in termination check");
  msg (wid, 3, "early termination check %s", res ? "succeeded" : "failed");
  return res;
}

static void flush (Worker * worker, int keep_locked) {
  int wid = worker - workers;
  int lit, idx, val, tmp, i;
  assert (worker->nunits);
  msg (wid, 2, "flushing %d units", worker->nunits);
  if (pthread_mutex_lock (&fixedmutex))
    warn ("failed to lock 'fixed' mutex in flush");
  flushed++;
  for (i = 0; i < worker->nunits; i++) {
    lit = worker->units[i];
    idx = abs (lit);
    assert (1 <= idx && idx <= nvars);
    assert (0 <= wid && wid < nworkers);
    worker->stats.units.calls++;
    val = (lit < 0) ? -1 : 1;
    tmp = vals[idx];
    if (!tmp) {
      assert (nfixed < nvars);
      fixed[nfixed++] = lit;
      vals[idx] = val;
      assert (!fixed[nfixed]);
      worker->stats.units.produced++;
      worker->stats.produced++;
      units++;
    } else if (tmp == -val) {
      if (pthread_mutex_lock (&donemutex))
	warn ("failed to lock 'done' mutex flushing unit");
      if (!globalres) msg (wid, 1, "mismatched unit");
      globalres = 20;
      done = 1;
      if (pthread_mutex_unlock (&donemutex)) 
	warn ("failed to unlock 'done' mutex flushing unit");
      break;
    } else assert (tmp == val);
  }
  worker->nunits = 0;
  if (keep_locked) return;
  if (pthread_mutex_unlock (&fixedmutex)) 
    warn ("failed to unlock 'fixed' mutex in flush");
}

static void produce (void * voidptr, int lit) {
  Worker * worker = voidptr;
  int wid = worker - workers;
  assert (worker->nunits < NUNITS);
  worker->units[worker->nunits++] = lit;
  msg (wid, 3, "producing unit %d", lit);
  if (worker->nunits == NUNITS) flush (worker, 0);
}

static void consume (void * voidptr, int ** fromptr, int ** toptr) {
  Worker * worker = voidptr;
  int wid = worker - workers;
  if (worker->nunits) flush (worker, 1);
  else if (pthread_mutex_lock (&fixedmutex))
    warn ("failed to lock 'fixed' mutex in consume");
  msg (wid, 3, "starting unit synchronization");
  syncs.units++;
  *fromptr = fixed + worker->fixed;
  *toptr = fixed + nfixed;
  if (pthread_mutex_unlock (&fixedmutex))
    warn ("failed to unlock 'fixed' in consume");
}

static int * lockrepr (void * voidptr) {
  Worker * worker = voidptr;
  int wid = worker - workers;
  if (pthread_mutex_lock (&reprmutex))
    warn ("failed to lock 'repr' mutex");
  msg (wid, 3, "starting equivalences synchronization");
  syncs.eqs++;
  return repr;
}

static void unlockrepr (void * voidptr, int consumed, int produced) {
  Worker * worker = voidptr;
  int wid = worker - workers;
  msg (wid, 3, 
       "finished equivalences synchronization: %d consumed, %d produced",
       consumed, produced);
  worker->stats.eqs.consumed += consumed;
  worker->stats.eqs.produced += produced;
  worker->stats.consumed += consumed;
  worker->stats.produced += produced;
  eqs += produced;
  assert (eqs < nvars);
  if (pthread_mutex_unlock (&reprmutex))
    warn ("failed to unlock 'repr' mutex");
}

static void consumed (void * voidptr, int consumed) {
  Worker * worker = voidptr;
  int wid = worker - workers;
  worker->stats.units.consumed += consumed;
  worker->stats.consumed += consumed;
  msg (wid, 3, "consuming %d units", consumed);
}

static void msglock (void * voidptr) {
  (void) voidptr;
  pthread_mutex_lock (&msgmutex);
}

static void msgunlock (void * voidptr) {
  (void) voidptr;
  pthread_mutex_unlock (&msgmutex);
}

static double percent (double a, double b) { return b ? (100 * a) / b : 0; }

static void * work (void * voidptr) {
  Worker * worker = voidptr;
  int wid = worker - workers;
  LGL * lgl = worker->lgl;
  assert (0 <= wid && wid < nworkers);
  msg (wid, 1, "running");
  assert (workers <= worker && worker < workers + nworkers);
  worker->res = lglsat (lgl);
  msg (wid, 1, "result %d", worker->res);
  if (pthread_mutex_lock (&donemutex))
    warn ("failed to lock 'done' mutex in worker");
  done = 1;
  if (pthread_mutex_unlock (&donemutex)) 
    warn ("failed to unlock 'done' mutex in worker");
  msg (wid, 2, "%d decisions, %d conflicts, %.0f props, %.1f MB",
       lglgetdecs (lgl), lglgetconfs (lgl), lglgetprops (lgl), lglmb (lgl));
  if (verbose >= 2) {
    if (pthread_mutex_lock (&fixedmutex))
      warn ("failed to lock 'fixed' in work");
    msg (wid, 2, "consumed %d units %.0f%%, produced %d units %.0f%%",
	 worker->stats.units.consumed, 
	 percent (worker->stats.units.consumed, nfixed),
	 worker->stats.units.produced, 
	 percent (worker->stats.units.produced, nfixed));
    if (pthread_mutex_unlock (&fixedmutex))
      warn ("failed to unlock 'fixed' in work");
  }
  return worker->res ? worker : 0;
}

static void setopt (int wid, const char * opt, int val) {
  Worker * w;
  LGL * lgl; 
  int old;
  assert (0 <= wid && wid < nworkers);
  w = workers + wid;
  lgl = w->lgl;
  assert (lglhasopt (lgl, opt));
  old = lglgetopt (lgl, opt);
  if (old == val) return;
  msg (wid, 1, "--%s=%d (instead of %d)", opt, val, old);
  lglsetopt (lgl, opt, val);
}

static void set10x (int wid, const char * opt) {
  int old, val;
  Worker * w;
  LGL * lgl; 
  assert (0 <= wid && wid < nworkers);
  w = workers + wid;
  lgl = w->lgl;
  assert (lglhasopt (lgl, opt));
  old = lglgetopt (lgl, opt);
  val = 10*old;
  msg (wid, 1, "--%s=%d (instead of %d)", opt, val, old);
  lglsetopt (lgl, opt, val);
}

static int getsystemcores (int explain) {
  int syscores, coreids = 0, res;
  FILE * p;
  syscores = sysconf (_SC_NPROCESSORS_ONLN);
  if (explain) {
    if (syscores > 0)
      msg (-1, 1, "'sysconf' reports %d processors online", syscores);
    else
      msg (-1, 1, "'sysconf' fails to determine number of online processors");
  }
  p = popen ("grep '^core id' /proc/cpuinfo 2>/dev/null|sort|uniq|wc -l", "r");
  if (p) {
    if (fscanf (p, "%d", &coreids) != 1) coreids = 0;
    if (explain) {
      if (coreids > 0) 
	msg (-1, 1, "found %d unique core ids in '/proc/cpuinfo'", coreids);
      else
	msg (-1, 1, "failed to extract core ids from '/proc/cpuinfo'");
    }
    pclose (p);
  }
  if ((coreids > 0 && syscores > 0 && coreids == syscores / 2) ||
      (coreids > 0 && coreids == syscores)) {
COREIDS:
    if (explain) 
      msg (-1, 1, 
           "assuming cores = extracted number of core ids = %d",
	   coreids);
    res = coreids;
  } else if (syscores > 0) {
    if (explain) 
      msg (-1, 1,
           "assuming cores = reported number of processors = %d",
           syscores);
    res = syscores;
  } else if (coreids > 0) goto COREIDS;
  else {
    if (explain) 
      msg (-1, 1, "using compiled in default value of %d workers", NWORKERS);
    res = NWORKERS;
  }
  return res;
}

static int cmproduced (const void * p, const void * q) {
  Worker * u = *(Worker**) p;
  Worker * v = *(Worker**) q;
  int res = v->stats.produced - u->stats.produced;
  if (res) return res;
  return u - v;
}

static int cmpconsumed (const void * p, const void * q) {
  Worker * u = *(Worker**) p;
  Worker * v = *(Worker**) q;
  int res = v->stats.consumed - u->stats.consumed;
  if (res) return res;
  return u - v;
}

static int parsenbcoreenv (void) {
  const char * str = getenv ("NBCORE");
  if (!str) return 0;
  if (!isposnum (str)) 
    die ("invalid value '%s' for environment variable NBCORE", str);
  return atoi (str);
}

int main (int argc, char ** argv) {
  Worker * w, * winner, *maxconsumer, * maxproducer, ** sorted;
  int i, res, clin, lit, val, id, nbcore, witness = 1;
  int sumconsumed, sumconsumedunits, sumconsumedeqs;
  const char * errstr, * arg;
  char * cmd;
  LGL * lgl;
  start = currentime ();
  clin = 0;
  for (i = 1; i < argc; i++) {
    if (!strcmp (argv[i], "-h")) {
      printf (
"usage: plingeling [-t <threads>][-h][-n][-p][-v]"
#ifndef NLGLOG
"[-l]"
#endif
"[<dimacs>[.gz]]\n"
"\n"
"  -t <num>   number of worker threads (default %d on this machine)\n"
"  -h         print this command line option summary\n"
"  -n         do not print solution / witness\n"
"  -p         plain portfolio, no sharing\n"
"  -d         do not share equivalences%s\n"
"  -e         share equivalences%s\n"
"  -v         increase verbose level\n"
"  -i         ignore additional clauses\n"
#ifndef NLGLOG
"  -l           increase log level\n"
#endif
, getsystemcores (0),
NOEQ ? " (default)" : "",
NOEQ ? "" : " (default)");
      exit (0);
    }
    if (!strcmp (argv[i], "-v")) verbose++;
#ifndef NLGLOG
    else if (!strcmp (argv[i], "-l")) loglevel++;
#endif
    else if (!strcmp (argv[i], "-i")) ignaddcls = 1;
    else if (!strcmp (argv[i], "-p")) plain = 1;
    else if (!strcmp (argv[i], "-d")) noeq = 1;
    else if (!strcmp (argv[i], "-n")) witness = 0;
    else if (!strcmp (argv[i], "-t")) {
      if (nworkers) die ("multiple '-t' arguments");
      if (i + 1 == argc) die ("argument to '-t' missing");
      else if (!isposnum (arg = argv[++i]) || (nworkers = atoi (arg)) <= 0)
	die ("invalid argument '%s' to '-t'", arg);
    } else if (argv[i][0] == '-') 
      die ("invalid option '%s' (try '-h')", argv[i]);
    else if (name) die ("multiple input files '%s' and '%s'", name, argv[i]);
    else name = argv[i];
  }
  if (verbose) lglbnr ("Plingeling", "c ", stdout), printf ("c\n");
  nbcore = parsenbcoreenv ();
  if (nworkers) {
    msg (-1, 1, 
	 "command line option '-t %d' overwrites system default %d",
	 nworkers, getsystemcores (0));
    if (nbcore)
      msg (-1, 1, 
           "and also overwrites environment variable NBCORE=%d",
	   nbcore);
  } else if (nbcore) {
    msg (-1, 1, 
	 "environment variable NBCORE=%d overwrites system default %d",
	 nbcore, getsystemcores (0));
    nworkers = nbcore;
  } else {
    msg (-1, 1,
      "no explicit specification of number of workers");
      nworkers = getsystemcores (1);
  }
  msg (-1, 1, "using %d workers", nworkers);
  NEW (workers, nworkers);
  for (i = 0; i < nworkers; i++) {
    w = workers + i;
    lgl = lglinit ();
    w->lgl = lgl;
    lglsetid (lgl, i, nworkers);
    lglsetime (lgl, getime);
    lglsetopt (lgl, "verbose", verbose);
#ifndef NLGLOG
    lglsetopt (lgl, "log", loglevel);
#endif
    setopt (i, "seed", i);
    setopt (i, "phase", -((i+1) % 3 - 1));
    switch (i&3) {
      default: val = 2; break;
      case 1: val = -1; break;
      case 2: val = 1; break;
    }
    setopt (i, "bias", val);
    if ((i&3)==1) set10x (i, "lftreleff");
    if ((i&3)==2) setopt (i, "elmnostr", 2);
    if (i == 3) setopt (i, "plain", 1);
    else if ((i&3)==3) set10x (i, "prbreleff");
    lglseterm (lgl, term, w);
    if (!plain) {
      lglsetproduceunit (lgl, produce, w);
      lglsetconsumeunits (lgl, consume, w);
      if (!noeq) {
	lglsetlockeq (lgl, lockrepr, w);
	lglsetunlockeq (lgl, unlockrepr, w);
      }
      lglsetconsumedunits (lgl, consumed, w);
      lglsetmsglock (lgl, msglock, msgunlock, w);
    }
    msg (i, 2, "initialized");
  }
  setsighandlers ();
  if (name) { 
    if (strlen (name) >= 3 && !strcmp (name + strlen(name) - 3, ".gz")) {
      cmd = malloc (strlen (name) + 30);
      sprintf (cmd, "gunzip -c %s 2>/dev/null", name);
      file = popen (cmd, "r");
      free (cmd);
      clin = 4;
    } else {
      file = fopen (name, "r");
      clin = 1;
    }
    if (!file) die ("can not read %s", name);
  } else file = stdin, name = "<stdin>";
  msg (-1, 1, "parsing %s", name);
  errstr = parse ();
  if (errstr) die ("parse error: %s", errstr);
  if (clin == 1) fclose (file);
  if (clin == 2) pclose (file);
  msg (-1, 2, "starting %d workers", nworkers);
  for (i = 0; i < nworkers; i++) {
    if (pthread_create (&workers[i].thread, 0, work, workers + i))
      die ("failed to create worker thread %d", i);
    msg (-1, 2, "started worker %d", i);
  }
  maxproducer = maxconsumer = winner = 0;
  res = 0;
  msg (-1, 2, "joining %d workers", nworkers);
  for (i = 0; i < nworkers; i++) {
    w = workers + i;
    if (pthread_join (w->thread, 0))
      die ("failed to join worker thread %d", i);
    msg (-1, 2, "joined worker %d", i);
    if (w->res) {
      if (!res) {
	res = w->res;
	winner = w;
	msg (-1, 1, "worker %d is the winner with result %d", i, res);
      } else if (res != w->res) die ("result discrepancy");
    }
    if (!maxconsumer || w->stats.consumed > maxconsumer->stats.consumed)
      maxconsumer = w;
    if (!maxproducer || w->stats.produced > maxproducer->stats.produced)
      maxproducer = w;
  }
  if (verbose) {
    NEW (sorted, nworkers);
    for (i = 0; i < nworkers; i++) sorted[i] = workers + i;
    printf ("c\n");
    assert (maxproducer);
    qsort (sorted, nworkers, sizeof *sorted, cmproduced);
    for (i = 0; i < nworkers; i++) {
      w = sorted[i];
      id = w - workers;
      printf (
        "c worker %2d %s %7d %3.0f%% = %7d units %3.0f%% + %7d eqs %3.0f%%\n",
	 id, (w == maxproducer ? "PRODUCED" : "produced"),
	 w->stats.produced, percent (w->stats.produced, units + eqs),
	 w->stats.units.produced, percent (w->stats.units.produced, units),
	 w->stats.eqs.produced, percent (w->stats.eqs.produced, eqs));
    }
    fputs ("c ", stdout);
    for (i = 0; i < 71; i++) fputc ('-', stdout);
    fputc ('\n', stdout);
    printf (
      "c           produced %7d 100%% = %7d units 100%% + %7d eqs 100%%\n",
      units + eqs, units, eqs);
    printf ("c\n");
    assert (maxconsumer);
    qsort (sorted, nworkers, sizeof *sorted, cmpconsumed);
    sumconsumed = sumconsumedunits = sumconsumedeqs =0;
    for (i = 0; i < nworkers; i++) {
      w = sorted[i];
      id = w - workers;
      sumconsumed += w->stats.consumed;
      sumconsumedeqs += w->stats.eqs.consumed;
      sumconsumedunits += w->stats.units.consumed;
      printf (
        "c worker %2d %s %7d %3.0f%% = %7d units %3.0f%% + %7d eqs %3.0f%%\n",
	id, (w == maxconsumer ? "CONSUMED" : "consumed"),
	w->stats.consumed, percent (w->stats.consumed, units + eqs),
	w->stats.units.consumed, percent (w->stats.units.consumed, units),
	w->stats.eqs.consumed, percent (w->stats.eqs.consumed, eqs));
    }
    fputs ("c ", stdout);
    for (i = 0; i < 71; i++) fputc ('-', stdout);
    fputc ('\n', stdout);
    printf (
      "c           consumed %7d 100%% = %7d units 100%% + %7d eqs 100%%\n",
      sumconsumed, sumconsumedunits, sumconsumedeqs);
    free (sorted);
    fflush (stdout);
  }
  if (!res) res = globalres;
  if (!res) die ("no result by any worker");
  assert (res);
  msg (-1, 2, "copying assignment");
  if (res == 10) {
    assert (winner);
    for (i = 1; i <= nvars; i++) {
      val = lglderef (winner->lgl, i);
      if (vals[i]) assert (val == vals[i]);
      vals[i] = val;
    }
  }
  resetsighandlers ();
  if (verbose) {
    for (i = 0; i < nworkers; i++) {
      printf ("c\nc ------------[worker %d statistics]------------ \nc\n", i);
      lglstats (workers[i].lgl, "c ", stdout);
    }
    printf ("c\nc -------------[overall statistics]------------- \nc\n");
    stats ();
    printf ("c\n");
  }
  msg (-1, 2, "releasing %d workers", nworkers);
  for (i = 0; i < nworkers; i++) {
    lglrelease (workers[i].lgl);
    msg (-1, 2, "released worker %d", i);
  }
  free (workers);
  free (fixed);
  if (!noeq) free (repr);
  if (verbose >= 2) printf ("c\n");
  if (res == 10) {
    printf ("s SATISFIABLE\n");
    if (witness) {
      fflush (stdout);
      if (nvars) printf ("v");
      for (i = 1; i <= nvars; i++) {
	if (!(i & 7)) fputs ("\nv", stdout);
	lit = vals[i] < 0 ? -i : i;
	printf (" %d", lit);
      }
      printf ("\nv 0\n");
    }
  } else if (res == 20) {
    printf ("s UNSATISFIABLE\n");
  } else printf ("s UNKNOWN\n");
  fflush (stdout);
  free (vals);
  return res;
}
