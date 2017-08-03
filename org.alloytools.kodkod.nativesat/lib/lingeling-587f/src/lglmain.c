/* Copyright 2010-2011 Armin Biere, Johannes Kepler University, Linz, Austria */

#include "lglib.h"

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>
#include <signal.h>
#include <unistd.h>

static LGL * lgl4sigh;
static int catchedsig, verbose, ignmissingheader, ignaddcls;

static void (*sig_int_handler)(int);
static void (*sig_segv_handler)(int);
static void (*sig_abrt_handler)(int);
static void (*sig_term_handler)(int);
static void (*sig_bus_handler)(int);

static void resetsighandlers (void) {
  (void) signal (SIGINT, sig_int_handler);
  (void) signal (SIGSEGV, sig_segv_handler);
  (void) signal (SIGABRT, sig_abrt_handler);
  (void) signal (SIGTERM, sig_term_handler);
  (void) signal (SIGBUS, sig_bus_handler);
}

static void caughtsigmsg (int sig) {
  if (!verbose) return;
  printf ("c\nc CAUGHT SIGNAL %d\nc\n", sig);
  fflush (stdout);
}

static void catchsig (int sig) {
  if (!catchedsig) {
    catchedsig = 1;
    caughtsigmsg (sig);
    if (verbose) {
      lglstats (lgl4sigh, "c ", stdout);
      caughtsigmsg (sig);
    }
  }
  resetsighandlers ();
  if (!getenv ("LGLNABORT")) raise (sig); else exit (1);
}

static void setsighandlers (void) {
  sig_int_handler = signal (SIGINT, catchsig);
  sig_segv_handler = signal (SIGSEGV, catchsig);
  sig_abrt_handler = signal (SIGABRT, catchsig);
  sig_term_handler = signal (SIGTERM, catchsig);
  sig_bus_handler = signal (SIGBUS, catchsig);
}

static int next (FILE * in, int *linenoptr) {
  int res = getc (in);
  if (res == '\n') *linenoptr += 1;
  return res;
}

static char isoptchartab[256];
static int isoptchartabinitialized;

static int isoptchar (unsigned char uch) { 
  int i;
  if (!isoptchartabinitialized) {
    for (i = 'a'; i <= 'z'; i++) isoptchartab[i] = 1;
    for (i = 'A'; i <= 'Z'; i++) isoptchartab[i] = 1;
    for (i = '0'; i <= '9'; i++) isoptchartab[i] = 1;
    isoptchartab['-'] = isoptchartab['_'] = 1;
    isoptchartabinitialized = 1;
  }
  return isoptchartab[uch];
}

typedef struct Opt { char * name; int size, count; } Opt;

static void pushoptch (Opt * opt, int ch) {
  if (opt->count + 1 >= opt->size)
   opt->name = realloc (opt->name, opt->size = opt->size ? 2*opt->size : 2);

  opt->name[opt->count++] = ch;
  opt->name[opt->count] = 0;
}

static const char * parse (LGL * lgl, FILE * in, int * lp) {
  int ch, prev, m, n, v, c, l, lit, sign, val, embedded = 0, header;
  Opt opt;
  memset (&opt, 0, sizeof opt);
SKIP:
  ch = next (in, lp);
  if (ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r') goto SKIP;
  if (ch == 'c') {
    ch  = next (in, lp);
    while (ch != '\n') {
      if (ch == EOF) return "end of file in comment";
      prev = ch;
      ch = next (in, lp);
      if (prev != '-') continue;
      if (ch != '-') continue;
      assert (!opt.count);
      ch = next (in, lp);
      while (isoptchar (ch)) {
	assert (ch != '\n');
	pushoptch (&opt, ch);
	ch = next (in, lp);
      }
      opt.count = 0;
      if (ch != '=') continue;
      ch = next (in, lp);
      if (ch == '-') sign = -1, ch = next (in, lp); else sign = 1;
      if (!isdigit (ch)) continue;
      val = ch - '0';
      while (isdigit (ch = next (in, lp)))
	val = 10 * val + (ch - '0');

      if (!lglhasopt (lgl, opt.name)) {
	fprintf (stderr, 
	         "*** lingeling warning: "
		 "parsed invalid embedded option '--%s'\n", 
		 opt.name);
	continue;
      }

      val *= sign;

      if (!embedded++ && verbose) printf ("c\nc embedded options:\nc\n");
      if (!strcmp (opt.name, "verbose")) verbose = val;
      if (verbose) printf ("c --%s=%d\n", opt.name, val);
      lglsetopt (lgl, opt.name, val);
    }
    goto SKIP;
  }
  free (opt.name);
  if (verbose) {
     if (embedded) printf ("c\n"); else printf ("c no embedded options\n");
     fflush (stdout);
  }
  header = m = n = v = l = c = 0;
  if (ignmissingheader) {
    if (ch == 'p')  {
      if (verbose) printf ("will not read header");
      while ((ch = next (in, lp)) != '\n' && ch != EOF)
	;
    } else if (verbose) printf ("c skipping missing header\n");
    goto BODY2;
  }
  if (ch != 'p') return "missing 'p ...' header";
  if (next (in, lp) != ' ') return "invalid header: expected ' ' after 'p'";
  if (next (in, lp) != 'c') return "invalid header: expected 'c' after ' '";
  if (next (in, lp) != 'n') return "invalid header: expected 'n' after 'c'";
  if (next (in, lp) != 'f') return "invalid header: expected 'f' after 'n'";
  if (next (in, lp) != ' ') return "invalid header: expected ' ' after 'f'";
  ch = next (in, lp);
  if (!isdigit (ch)) return "invalid header: expected digit after 'p cnf '";
  m = ch - '0';
  while (isdigit (ch = next (in, lp)))
    m = 10 * m + (ch - '0');
  if (ch != ' ') return "invalid header: expected ' ' after 'p cnf <m>'"; 
  ch = next (in, lp);
  if (!isdigit (ch)) 
    return "invalid header: expected digit after 'p cnf <m> '";
  n = ch - '0';
  while (isdigit (ch = next (in, lp)))
    n = 10 * n + (ch - '0');
  while (ch == ' ')
    ch = next (in, lp);
  if (ch != '\n') return "invalid header: expected new line after header";
  if (verbose) printf ("c found 'p cnf %d %d' header\n", m, n);
  header = 1;
BODY:
  ch = next (in, lp);
BODY2:
  if (ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r') goto BODY;
  if (ch == 'c') {
    while ((ch = next (in, lp)) != '\n')
      if (ch == EOF) return "end of file in comment";
    goto BODY;
  }
  if (ch == EOF) {
    if (header && c + 1 == n) return "clause missing";
    if (header && c < n) return "clauses missing";
DONE:
    if (verbose) 
      printf ("c read %d variables, %d clauses, %d literals in %.1f seconds\n", 
	      v, c, l, lglsec (lgl));
    return 0;
  }
  if (ch == '-') {
    ch = next (in, lp);
    if (ch == '0') return "expected positive digit after '-'";
    sign = -1;
  } else sign = 1;
  if (!isdigit (ch)) return "expected digit";
  if (header && c == n) return "too many clauses";
  lit = ch - '0';
  while (isdigit (ch = next (in, lp)))
    lit = 10 * lit + (ch - '0');
  if (header && lit > m) return "maxium variable index exceeded";
  if (lit > v) v = lit;
  if (lit) l++;
  else c++;
  lit *= sign;
  lgladd (lgl, lit);
  if (!lit && ignaddcls && c == n) goto DONE;
  goto BODY;
}

typedef struct OBuf { char line[81]; int pos; } OBuf;

static void flushobuf (OBuf * obuf) {
  assert (0 < obuf->pos);
  assert (obuf->pos < 81);
  obuf->line[obuf->pos++] = '\n';
  assert (obuf->pos < 81);
  obuf->line[obuf->pos++] = 0;
  fputc ('v', stdout);
  fputs (obuf->line, stdout);
  obuf->pos = 0;
}

static void print2obuf (OBuf * obuf, int i) {
  char str[20];
  int len;
  sprintf (str, " %d", i);
  len = strlen (str);
  assert (len > 1);
  if (obuf->pos + len > 79) flushobuf (obuf);
  strcpy (obuf->line + obuf->pos, str);
  obuf->pos += len;
  assert (obuf->pos <= 79);
}

int main (int argc, char ** argv) {
  const char * name = 0, * wtrn = 0, * match, * p, * err;
  int res = 0, i, j, clin = 0, val, len, lineno = 1, cltr = 0;
  FILE * in, * wtrf = 0;
  int maxvar, lit;
  char * tmp;
  LGL * lgl;
  OBuf obuf;
  lgl4sigh = lgl = lglinit ();
  setsighandlers ();
  for (i = 1; i < argc; i++) {
    if (strncmp (argv[i], "--write-api-trace=", 18)) continue;
                         //123456789012345678
    if (wtrn) {
      fprintf (stderr, 
               "*** lingeling error: can not write API trace '%s' and '%s'\n",
               wtrn, argv[i]);
      res = 1;
      goto DONE;
    }
    wtrn = argv[i] + 18;
    printf ("%s\n", wtrn);
  }
  if (wtrn) { 
    len = strlen (wtrn);
    if (len >= 3 && !strcmp (wtrn + len - 3, ".gz")) {
      tmp = malloc (len + 20);
      unlink (wtrn);
      sprintf (tmp, "gzip -c > %s", wtrn);
      wtrf = popen (tmp, "w");
      if (wtrf) cltr = 2;
      free (tmp);
    } else {
      wtrf = fopen (wtrn, "w");
      if (wtrf) cltr = 1;
    }
    if (!wtrf) {
      fprintf (stderr, "*** lingeling error: can not write %s\n", wtrn);
      res = 1;
      goto DONE;
    }
    lglwtrapi (lgl, wtrf);
  }
  for (i = 1; i < argc; i++) {
    if (!strcmp (argv[i], "-h") || !strcmp (argv[i], "--help")) {
      printf ("usage: lingeling [<option> ...][<file>[.gz]]\n");
      printf ("\n");
      printf ("where <option> is one of the following:\n");
      printf ("\n");
      printf ("-h|--help        print command line option summary\n");
      printf ("-f|--force       force reading even without header\n");
      printf ("-i|--ignore      ignore additional clauses\n");
      printf ("-r|--ranges      print value ranges of options\n");
      printf ("-d|--defaults    print default values of options\n");
      printf ("-e|--embedded    dito but in an embedded format print\n");
      printf ("-n|--nowitness   no solution (see '--witness')\n");
      printf ("\n");
      printf ("--write-api-trace=<file> trace and write API calls\n");
      printf ("\n");
      printf (
"The following options can also be used in the form '--<name>=<int>',\n"
"just '--<name>' for increment and '--no-<name>' for zero.  They\n"
"can be embedded into the CNF file, set through the API or capitalized\n"
"with prefix 'LGL' instead of '--' through environment variables.\n"
"Their default values are displayed in square brackets, explicitly\n"
"at higher verbose levels or with the command line options '-d' and\n"
"'--defaults'.\n");
      printf ("\n");
      lglusage (lgl);
      goto DONE;
    } else if (!strcmp (argv[i], "-d") || !strcmp (argv[i], "--defaults")) {
      lglopts (lgl, "", 0);
      goto DONE;
    } else if (!strcmp (argv[i], "-e") || !strcmp (argv[i], "--embedded")) {
      lglopts (lgl, "c ", 1);
      goto DONE;
    } else if (!strcmp (argv[i], "-r") || !strcmp (argv[i], "--ranges")) {
      lglrgopts (lgl);
      goto DONE;
    } else if (!strcmp (argv[i], "-f") || !strcmp (argv[i], "--force")) {
      ignmissingheader = 1;
    } else if (!strcmp (argv[i], "-i") || !strcmp (argv[i], "--ignore")) {
      ignaddcls = 1;
    } else if (!strcmp (argv[i], "-n") || !strcmp (argv[i], "nowitness")) {
      lglsetopt (lgl, "witness", 0);
    } else if (argv[i][0] == '-') {
      if (argv[i][1] == '-') {
	match = strchr (argv[i] + 2, '=');
	if (match) {
	  p = match + 1;
	  if (*p == '-') p++;
	  len = p - argv[i];
	  if (!strncmp (argv[i], "--write-api-trace=", len)) continue;
	  else if (!isdigit (*p)) {
ERR:
            fprintf (stderr,
	             "*** lingeling error: "
		     " invalid command line option '%s'\n",
	             argv[i]);
	    res = 1;
	    goto DONE;
	  }
	  while (*++p) if (!isdigit (*p)) goto ERR;
	  len = match - argv[i] - 2;
	  tmp = malloc (len + 1);
	  j = 0;
	  for (p = argv[i] + 2; *p != '='; p++) tmp[j++] = *p;
	  tmp[j] = 0;
	  val = atoi (match + 1);
	} else if (!strncmp (argv[i], "--no-", 5)) {
	  tmp = strdup (argv[i] + 5);
	  val = 0;
	} else {
	  tmp = strdup (argv[i] + 2);
	  val = lglgetopt (lgl, tmp) + 1;
	}
	if (!lglhasopt (lgl, tmp)) { free (tmp); goto ERR; }
	lglsetopt (lgl, tmp, val);
	free (tmp);
      } else {
	if (argv[i][2]) goto ERR;
	if (!lglhasopt (lgl, argv[i] + 1)) goto ERR;
	val = lglgetopt (lgl, argv[i] + 1) + 1;
	lglsetopt (lgl, argv[i] + 1, val);
      }
    } else if (name) {
      fprintf (stderr, "*** lingeling error: can not read '%s' and '%s'\n",
               name, argv[i]);
      res = 1;
      goto DONE;
    } else name = argv[i];
  }
  verbose = lglgetopt (lgl, "verbose");
  if (verbose) lglbnr ("Lingeling", "c ", stdout);
  if (verbose >= 2) {
   printf ("c\nc options after command line parsing:\nc\n");
   lglopts (lgl, "c ", 0);
   printf ("c\n");
   lglsizes ();
   printf ("c\n");
  }
  if (name) {
    len = strlen (name);
    if (len >= 3 && !strcmp (name + len - 3, ".gz")) {
      tmp = malloc (len + 20);
      sprintf (tmp, "gunzip -c %s", name);
      in = popen (tmp, "r");
      if (in) clin = 2;
      free (tmp);
    } else {
      in = fopen (name, "r");
      if (in) clin = 1;
    }
    if (!in) {
      fprintf (stderr, "*** lingeling error: can not read %s\n", name);
      res = 1;
      goto DONE;
    }
  } else name = "<stdin>", in = stdin;
  if (verbose) printf ("c reading %s\n", name);
  fflush (stdout);
  if ((err = parse (lgl, in, &lineno))) {
    fprintf (stderr, "%s:%d: %s\n", name, lineno, err);
    res = 1;
    goto DONE;
  }
  if (clin == 1) fclose (in);
  if (clin == 2) pclose (in);
  clin = 0;
  if (verbose) {
    printf ("c\n");
    if (verbose >= 2) printf ("c final options:\nc\n");
    lglopts (lgl, "c ", 0);
  }
  res = lglsat (lgl);
  if (verbose) lglstats (lgl, "c ", stdout), fputs ("c\n", stdout);
  if (res == 10) fputs ("s SATISFIABLE\n", stdout);
  else if (res == 20) fputs ("s UNSATISFIABLE\n", stdout);
  else fputs ("s UNKNOWN\n", stdout);
  fflush (stdout);
  if (res == 10 && lglgetopt (lgl, "witness")) {
    obuf.pos = 0;
    maxvar = lglmaxvar (lgl);
    for (i = 1; i <= maxvar; i++) {
      lit = (lglderef (lgl, i) > 0) ? i : -i;
      print2obuf (&obuf, lit);
    }
    print2obuf (&obuf, 0);
    if (obuf.pos > 0) flushobuf (&obuf);
    fflush (stdout);
  }
DONE:
  if (clin == 1) fclose (in);
  if (clin == 2) pclose (in);
  resetsighandlers ();
  lgl4sigh = 0;
  lglrelease (lgl);
  if (cltr == 1) fclose (wtrf);
  if (cltr == 2) pclose (wtrf);
  return res;
}
