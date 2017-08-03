/* Copyright 2010-2011 Armin Biere, Johannes Kepler University, Linz, Austria */

#ifndef lglib_h_INCLUDED
#define lglib_h_INCLUDED

#include <stdio.h>				// for 'FILE'
#include <stdlib.h>				// for 'int64_t'

typedef struct LGL LGL;

LGL * lglinit (void);				// constructor
void lglrelease (LGL *);			// destructor

void lglsetopt (LGL *, const char *, int);	// set option value
int lglgetopt (LGL *, const char *);		// get option value
int lglhasopt (LGL *, const char *);		// exists option?
void lglusage (LGL *);				// print usage "-h"
void lglopts (LGL *, const char * prefix, int);	// ... defaults "-d" | "-e"
void lglrgopts (LGL *);				// ... option ranges "-r"
void lglbnr (const char * name,
             const char * prefix,
	     FILE * file);			// ... banner
void lglsizes (void);				// ... data structure sizes

void * lglfirstopt (LGL *);
void * lglnextopt (LGL *, 
                   void * iterator, 
                   const char ** nameptr,
		   int *valptr, int *minptr, int *maxptr);

// call back for abort
void lglonabort (LGL *, void * state, void (*callback)(void* state));

// write and read API trace
void lglwtrapi (LGL *, FILE *);
void lglrtrapi (LGL *, FILE *);

// main interface as in PicoSAT:
int lglmaxvar (LGL *);
void lgladd (LGL *, int lit);
void lglassume (LGL *, int lit);		// currently only one!
int lglsat (LGL *);
int lglderef (LGL *, int lit);			// neg=false, pos=true

// incremental interface
void lglfreeze (LGL *, int lit);
void lglmelt (LGL *, int lit);

// stats:
void lglstats (LGL *, const char * prefix, FILE *);
int64_t lglgetconfs (LGL *);
int64_t lglgetdecs (LGL *);
int64_t lglgetprops (LGL *);
double lglmb (LGL *);
double lglmaxmb (LGL *);
double lglsec (LGL *);
double lglprocesstime (void);

// core threaded support:

void lglseterm (LGL *, int (*term)(void*), void*);

void lglsetproduceunit (LGL *, void (*produce)(void*, int), void*);
void lglsetconsumeunits (LGL *, void (*consume)(void*,int**,int**), void*);

void lglsetlockeq (LGL *, int * (*lock)(void*), void *);
void lglsetunlockeq (LGL *, void (*unlock)(void*,int cons,int prod), void *);

// threaded support for logging and statistics:
void lglsetid (LGL *, int tid, int tids);

void lglsetconsumedunits (LGL *, void (*consumed)(void*,int), void*);

void lglsetmsglock (LGL *, void (*lock)(void*), void (*unlock)(void*), void*);
void lglsetime (LGL *, double (*time)(void));

// term: called regularly if set: terminate if non zero return value
// produce: called for each derived unit if set
// consume: called regularly if set: import derived units
// lock: return zero terminated vector of externally derived units
// unlock: unlock using the locked list and return number of consumed units

#endif
