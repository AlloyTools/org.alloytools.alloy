/**
 * Implementation of the MiniSAT specification in Java.
 *
 * Some classes have been added in order to allow testing several heuristics and learning scheme
 * but the solver is still very close to the original MiniSAT.
 * 
 * For sake of efficiency, some tradeoff with OOP were made: literals are here represented by integers
 * whose attributes are stored in a {@link org.sat4j.minisat.constraints.cnf.Lits} (vocabulary) object.
 * 
 * A factory of solvers is provided for a friendly access to prebuilt solvers.
 */

package org.sat4j.minisat;

