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
package org.sat4j.tools;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.logging.Logger;

import org.sat4j.annotations.Feature;
import org.sat4j.core.LiteralsUtils;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolverService;
import org.sat4j.specs.Lbool;
import org.sat4j.specs.SearchListenerAdapter;

/**
 * Output an unsat proof using the reverse unit propagation (RUP) format.
 * 
 * @author daniel
 * 
 * @param <S>
 *            a solver service
 * @since 2.3.4
 */
@Feature("searchlistener")
public class RupSearchListener<S extends ISolverService>
        extends SearchListenerAdapter<S> {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    private PrintStream out;
    private final File file;

    public RupSearchListener(String filename) {
        file = new File(filename);
    }

    @Override
    public void init(S solverService) {
        try {
            out = new PrintStream(new FileOutputStream(file));
        } catch (FileNotFoundException e) {
            out = System.out;
        }
    }

    @Override
    public void end(Lbool result) {
        if (result == Lbool.FALSE) {
            out.println("0");
            out.close();
        } else {
            out.close();
            if (!file.delete()) {
                Logger.getLogger("org.sat4j.core")
                        .info("Cannot delete file " + file.getName());
            }
        }
    }

    @Override
    public void learn(IConstr c) {
        printConstr(c);
    }

    @Override
    public void delete(IConstr c) {
        out.print("d ");
        printConstr(c);
    }

    private void printConstr(IConstr c) {
        for (int i = 0; i < c.size(); i++) {
            out.print(LiteralsUtils.toDimacs(c.get(i)));
            out.print(" ");
        }
        out.println("0");
    }

    @Override
    public void learnUnit(int p) {
        out.print(p);
        out.println(" 0");
    }

}
