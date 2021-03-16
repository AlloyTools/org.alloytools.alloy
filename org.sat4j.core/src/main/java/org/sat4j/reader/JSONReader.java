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
package org.sat4j.reader;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.sat4j.annotations.Feature;
import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;

/**
 * Simple JSON reader for clauses and cardinality constraints.
 * 
 * Clauses are represented as an array of Dimacs literals (non zero integers).
 * Cardinality constraints are represented like a clause for its left hand side,
 * a comparator (a string) and a number.
 * <code>[[-1,-2,-3],[[1,-2,3],'&gt;',2],[4,-3,6]]</code> for instance
 * represents three constraints, two clauses and the cardinality constraint
 * <code>x1 + not x2 + x3 &gt; 2</code>.
 * 
 * @author leberre
 * 
 * @param <S>
 *            the type of solver to feed.
 * @since 2.3.3
 */
@Feature(value = "reader", parent = "expert")
public class JSONReader<S extends ISolver> extends Reader {

    protected final S solver;

    public static final String CLAUSE = "(\\[(-?(\\d+)(,-?(\\d+))*)?\\])";

    public static final String CARD = "(\\[" + CLAUSE + ",'[=<>]=?',-?\\d+\\])";

    public final String constraint;

    public final String formula;

    private static final Pattern CLAUSE_PATTERN = Pattern.compile(CLAUSE);

    private static final Pattern CARD_PATTERN = Pattern.compile(CARD);

    private final Pattern constraintPattern;

    public JSONReader(S solver) {
        this.solver = solver;
        constraint = constraintRegexp();
        formula = "^\\[(" + constraint + "(," + constraint + ")*)?\\]$";
        constraintPattern = Pattern.compile(constraint);
    }

    protected String constraintRegexp() {
        return "(" + CLAUSE + "|" + CARD + ")";
    }

    private void handleConstraint(String constraint)
            throws ParseFormatException, ContradictionException {
        if (CARD_PATTERN.matcher(constraint).matches()) {
            handleCard(constraint);
        } else if (CLAUSE_PATTERN.matcher(constraint).matches()) {
            handleClause(constraint);
        } else {
            handleNotHandled(constraint);
        }
    }

    protected void handleNotHandled(String constraint)
            throws ParseFormatException, ContradictionException {
        throw new ParseFormatException("Unknown constraint: " + constraint);
    }

    private void handleClause(String constraint)
            throws ParseFormatException, ContradictionException {
        solver.addClause(getLiterals(constraint));
    }

    protected IVecInt getLiterals(String constraint)
            throws ParseFormatException {
        String trimmed = constraint.trim();
        trimmed = trimmed.substring(1, trimmed.length() - 1);
        String[] literals = trimmed.split(",");
        IVecInt clause = new VecInt();
        for (String literal : literals) {
            if (literal.length() > 0)
                clause.push(Integer.valueOf(literal.trim()));
        }
        return clause;
    }

    protected void handleCard(String constraint)
            throws ParseFormatException, ContradictionException {
        String trimmed = constraint.trim();
        trimmed = trimmed.substring(1, trimmed.length() - 1);
        Matcher matcher = CLAUSE_PATTERN.matcher(trimmed);
        if (matcher.find()) {
            IVecInt clause = getLiterals(matcher.group());
            trimmed = matcher.replaceFirst("");
            String[] str = trimmed.split(",");

            int degree = Integer.valueOf(str[2]);
            String comparator = str[1].substring(1, str[1].length() - 1);
            if ("=".equals(comparator) || ("==".equals(comparator))) {
                solver.addExactly(clause, degree);
            } else if ("<=".equals(comparator)) {
                solver.addAtMost(clause, degree);
            } else if ("<".equals(comparator)) {
                solver.addAtMost(clause, degree - 1);
            } else if (">=".equals(comparator)) {
                solver.addAtLeast(clause, degree);
            } else if (">".equals(comparator)) {
                solver.addAtLeast(clause, degree + 1);
            }
        }
    }

    @Override
    public IProblem parseInstance(InputStream in)
            throws ParseFormatException, ContradictionException, IOException {
        StringWriter out = new StringWriter();
        BufferedReader reader = new BufferedReader(new InputStreamReader(in));
        String line;
        while ((line = reader.readLine()) != null) {
            out.append(line);
        }
        return parseString(out.toString());
    }

    public ISolver parseString(String json)
            throws ParseFormatException, ContradictionException {
        String trimmed = json.trim();
        if (!trimmed.matches(formula)) {
            throw new ParseFormatException("Wrong input " + json);
        }
        Matcher matcher = constraintPattern.matcher(trimmed);
        while (matcher.find()) {
            handleConstraint(matcher.group());
        }
        return solver;
    }

    @Override
    @Deprecated
    public String decode(int[] model) {
        return "[" + new VecInt(model) + "]";
    }

    @Override
    public void decode(int[] model, PrintWriter out) {
        out.print("[");
        out.print(new VecInt(model));
        out.print("]");
    }

}
