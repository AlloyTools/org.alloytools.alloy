
#include <jni.h>
#include "cmsat/Solver.h"
#include "kodkod_engine_satlab_CryptoMiniSat.h"
#include <iostream>

using namespace CMSat;
using namespace std;
/*
 * Class:     kodkod_engine_satlab_CryptoMiniSat
 * Method:    make
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL Java_kodkod_engine_satlab_CryptoMiniSat_make
(JNIEnv *, jclass) {
	/*SolverConf conf;
	conf.fixRestartType = static_restart;
	conf.polarity_mode = polarity_false;
	conf.doFindXors= false;
	conf.doPartHandler = false;
	Solver* solver = new Solver(conf);
	return ((jlong) solver);*/
	Solver* solver = new Solver();
	return ((jlong) solver);
}

/*
 * Class:     kodkod_engine_satlab_CryptoMiniSat
 * Method:    free
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_kodkod_engine_satlab_CryptoMiniSat_free
(JNIEnv *, jobject, jlong solver) {
	delete ((Solver*)solver);
}

/*
 * Class:     kodkod_engine_satlab_CryptoMiniSat
 * Method:    addVariables
 * Signature: (JI)V
 */
JNIEXPORT void JNICALL Java_kodkod_engine_satlab_CryptoMiniSat_addVariables
(JNIEnv * env, jobject, jlong solver, jint  numVars) {
	Solver* solverPtr = (Solver*) solver;
	//SolverConf conf = solverPtr->conf;
	/*std::cout << (conf.fixRestartType == static_restart);
	std::cout << (conf.polarity_mode == polarity_false);
	std::cout << (conf.doFindXors);
	std::cout << (conf.doPartHandler);*/
	for(int i = 0; i < numVars; ++i) {
		solverPtr->newVar();
	}
}

/*
 * Class:     kodkod_engine_satlab_CryptoMiniSat
 * Method:    addClause
 * Signature: (J[I)Z
 */
JNIEXPORT jboolean JNICALL Java_kodkod_engine_satlab_CryptoMiniSat_addClause
(JNIEnv * env, jobject, jlong solver, jintArray clause) {
	jsize length = env->GetArrayLength(clause);
	jint* buf = env->GetIntArrayElements(clause, JNI_FALSE);
	Solver* solverPtr = ((Solver*)solver);
	vec<Lit> lits;
	for(int i = 0; i < length; ++i) {
		int lit = *(buf+i);
		int var = abs(lit)-1;
		lits.push((lit > 0) ?  Lit(var, false) : Lit(var, true));
	}
	solverPtr->addClause(lits);
	env->ReleaseIntArrayElements(clause, buf, 0);
	return solverPtr->okay();
}

/*
 * Class:     kodkod_engine_satlab_CryptoMiniSat
 * Method:    solve
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_kodkod_engine_satlab_CryptoMiniSat_solve
(JNIEnv *, jobject, jlong solver) {
	return ((Solver*)solver)->solve()==l_True;
}

/*
 * Class:     kodkod_engine_satlab_CryptoMiniSat
 * Method:    valueOf
 * Signature: (JI)Z
 */
JNIEXPORT jboolean JNICALL Java_kodkod_engine_satlab_CryptoMiniSat_valueOf
(JNIEnv *, jobject, jlong solver, jint var) {
	return ((Solver*)solver)->model[var-1]==l_True;
}
