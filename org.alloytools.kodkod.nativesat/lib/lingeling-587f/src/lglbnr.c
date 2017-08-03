/* Copyright 2010-2011 Armin Biere Johannes Kepler University Linz Austria */

#include "lglib.h"
#include "lglcfg.h"
#include "lglcflags.h"

#include <stdio.h>
#include <string.h>
#include <assert.h>

void lglbnr (const char * name, const char * prefix, FILE * file) {
  const char * p = LGL_CFLAGS, * q, * n;
  int len = 78 - strlen (prefix);
  fprintf (file, "%s%s Version %s %s\n", prefix, name, LGL_VERSION, LGL_ID);
  fprintf (file,
           "%sCopyright (C) 2010-2011 Armin Biere JKU Linz Austria."
           "  All rights reserved.\n", prefix);
  fprintf (file, "%sreleased %s\n", prefix, LGL_RELEASED);
  fprintf (file, "%scompiled %s\n", prefix, LGL_COMPILED);
  fprintf (file, "%s%s\n", prefix, LGL_CC);
  assert (*p);
  for (;;) {
    fputs (prefix, file);
    for (q = p; *q && *q != ' '; q++)
      ;
    if (*q && q - p < len) {
      for (;;) {
	for (n = q + 1; *n && *n != ' '; n++)
	  ;
	if (n - p >= len) break;
	q = n;
	if (!*n) break;
      }
    }
    while (p < q) fputc (*p++, file);
    fputc ('\n', file);
    if (!*p) break;
    assert(*p == ' ');
    p++;
  }
  fprintf (file, "%s%s\n", prefix, LGL_OS);
  fflush (file);
}
