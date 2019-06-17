#include <jni.h>

#include "kodkod_engine_satlab_Glucose41.h"
#include "core/Solver.h"
#include <iostream>
#include <cstdlib>
#include <cstdio>
#include <cstring>

using namespace Glucose;

/*
 * Class:     kodkod_engine_satlab_Glucose41
 * Method:    make
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL Java_kodkod_engine_satlab_Glucose41_make
(JNIEnv *, jclass) {
	Solver* solver = new Solver();
	solver->verbosity = 0;
	//std::cout << "creating " << ((jlong) solver) << "\n";
	return ((jlong) solver);
}

/*
 * Class:     kodkod_engine_satlab_Glucose41
 * Method:    free
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_kodkod_engine_satlab_Glucose41_free
(JNIEnv *, jobject, jlong solver) {
	//std::cout << "destroying " << solver << "\n";
	delete ((Solver*)solver);
}
/*
 * Class:     kodkod_engine_satlab_Glucose41
 * Method:    addVariables
 * Signature: (JI)V
 */
JNIEXPORT void JNICALL Java_kodkod_engine_satlab_Glucose41_addVariables
(JNIEnv *, jobject, jlong solver, jint  numVars) {
	Solver* solverPtr = (Solver*) solver;
	for(int i = 0; i < numVars; ++i) {
		solverPtr->newVar();
	}
}

/*
 * Class:     kodkod_engine_satlab_Glucose41
 * Method:    addClause
 * Signature: (J[I)Z
 */
JNIEXPORT jboolean JNICALL Java_kodkod_engine_satlab_Glucose41_addClause
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
 * Class:     kodkod_engine_satlab_Glucose41
 * Method:    solve
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_kodkod_engine_satlab_Glucose41_solve
(JNIEnv *, jobject, jlong solver) {
	//std::cout << "-> p cnf " << ((Solver*)solver)->nVars() << " " <<  ((Solver*)solver)->nClauses() << "\n";
	return ((Solver*)solver)->solve();
}

/*
 * Class:     kodkod_engine_satlab_Glucose41
 * Method:    valueOf
 * Signature: (JI)Z
 */
JNIEXPORT jboolean JNICALL Java_kodkod_engine_satlab_Glucose41_valueOf
(JNIEnv *, jobject, jlong solver, jint var) {
	return ((Solver*)solver)->model[var-1]==l_True;
}
