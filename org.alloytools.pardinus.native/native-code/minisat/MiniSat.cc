#include <iostream>
#include <cstdlib>
#include <cstdio>
#include <cstring>
#include <cassert>

#include <map>
#include <set>
#include <vector>
#include <list>
#include <string>
#include <algorithm>
#include <queue>

#include <jni.h>
#include <minisat/core/Solver.h>
#include "AlloyMiniSat.h"

#define NS(name) Java_org_alloytools_solvers_natv_minisat_MiniSat_ ## name

using namespace Minisat;


/*
 * Class:     kodkod_engine_satlab_MiniSat
 * Method:    make
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL NS(make)
  (JNIEnv *, jclass) {
  Solver* solver = new Solver();
  return ((jlong) solver);
}

/*
 * Class:     kodkod_engine_satlab_MiniSat
 * Method:    free
 * Signature: (J)V
 */
JNIEXPORT void JNICALL NS(free)
  (JNIEnv *, jobject, jlong solver) {
  delete ((Solver*)solver);  
}

/*
 * Class:     kodkod_engine_satlab_MiniSat
 * Method:    addVariables
 * Signature: (JI)V
 */
JNIEXPORT void JNICALL NS(addVariables)
  (JNIEnv *, jobject, jlong solver, jint  numVars) {
  Solver* solverPtr = (Solver*) solver;
  for(int i = 0; i < numVars; ++i) {
     solverPtr->newVar();
  }
}

/*
 * Class:     kodkod_engine_satlab_MiniSat
 * Method:    addClause
 * Signature: (J[I)Z
 */
JNIEXPORT jboolean JNICALL NS(addClause)
  (JNIEnv * env, jobject, jlong solver, jintArray clause) {
    jsize length = env->GetArrayLength(clause);
    jint* buf = env->GetIntArrayElements(clause, JNI_FALSE);
    Solver* solverPtr = ((Solver*)solver);
    vec<Lit> lits;
    for(int i = 0; i < length; ++i) {
        int var = *(buf+i);
        lits.push((var > 0) ?  mkLit(var-1) : ~mkLit(-var-1));
    }
    solverPtr->addClause(lits);
    env->ReleaseIntArrayElements(clause, buf, 0);
    return solverPtr->okay();
 }

/*
 * Class:     kodkod_engine_satlab_MiniSat
 * Method:    solve
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL NS(solve)
  (JNIEnv *, jobject, jlong solver) {
   return ((Solver*)solver)->solve();
  }

/*
 * Class:     kodkod_engine_satlab_MiniSat
 * Method:    valueOf
 * Signature: (JI)Z
 */
JNIEXPORT jboolean JNICALL NS(valueOf)
  (JNIEnv *, jobject, jlong solver, jint var) {
  return ((Solver*)solver)->model[var-1]==l_True;
 }

