/*******************************************************************************
 * SAT4J: a SATisfiability library for Java Copyright (C) 2004, 2012 Artois University and CNRS
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 *  http://www.eclipse.org/legal/epl-v10.html
 *
 * Alternatively, the contents of this file may be used under the terms of
 * either the GNU Lesser General Public License Version 2.1 or later (the
 * "LGPL"), in which case the provisions of the LGPL are applicable instead
 * of those above. If you wish to allow use of your version of this file only
 * under the terms of the LGPL, and not to allow others to use your version of
 * this file under the terms of the EPL, indicate your decision by deleting
 * the provisions above and replace them with the notice and other provisions
 * required by the LGPL. If you do not delete the provisions above, a recipient
 * may use your version of this file under the terms of the EPL or the LGPL.
 *
 * Based on the original MiniSat specification from:
 *
 * An extensible SAT solver. Niklas Een and Niklas Sorensson. Proceedings of the
 * Sixth International Conference on Theory and Applications of Satisfiability
 * Testing, LNCS 2919, pp 502-518, 2003.
 *
 * See www.minisat.se for the original solver in C++.
 *
 * Contributors:
 *   CRIL - initial API and implementation
 *******************************************************************************/
package org.sat4j.minisat.learning;

import org.sat4j.annotations.Feature;
import org.sat4j.minisat.core.DataStructureFactory;
import org.sat4j.minisat.core.Solver;
import org.sat4j.specs.Constr;

/**
 * MiniSAT learning scheme.
 * 
 * The Data Structure Factory is expected to be set thanks to the appropriate
 * setter method before using it.
 * 
 * It was not possible to set it in the constructor.
 * 
 * @author leberre
 */
@Feature(value = "learning", parent = "expert")
public final class MiniSATLearning<D extends DataStructureFactory>
        extends AbstractLearning<D> {
    private static final long serialVersionUID = 1L;

    private DataStructureFactory dsf;

    public void setDataStructureFactory(DataStructureFactory dsf) {
        this.dsf = dsf;
    }

    @Override
    public void setSolver(Solver<D> s) {
        super.setSolver(s);
        if (s != null) {
            this.dsf = s.getDSFactory();
        }
    }

    public void learns(Constr constr) {
        // va contenir une nouvelle clause ou null si la clause est unitaire
        claBumpActivity(constr);
        this.dsf.learnConstraint(constr);
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return "Learn all clauses as in MiniSAT";
    }

}
