/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.translator;

import static kodkod.engine.Solution.Outcome.SATISFIABLE;
import static kodkod.engine.Solution.Outcome.TRIVIALLY_SATISFIABLE;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import kodkod.ast.BinaryExpression;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;

/**
 * Immutable; this class stores the set of solutions from the book, for teaching
 * purpose, so that users of the tool will see the same illustration as the book
 * and not get confused by SAT solver nondeterminism.
 */

final class BookExamples {

    // It calls the following methods on a bounds-computed A4Solution object:
    // getAllReachableSigs(), getFactory(), getBounds(), a2k(), kr2typeCLEAR()

    /**
     * Returns the Sig if the list of sig contains a sig with the given label, else
     * returns null.
     */
    private static Sig hasSig(Iterable<Sig> sigs, String label) {
        for (Sig s : sigs)
            if (s.label.equals(label))
                return s;
        return null;
    }

    /**
     * If one of the solution is a solution to the given problem, return it, else
     * return null.
     */
    static Solution trial(A4Reporter rep, A4Solution frame, Formula formula, Solver solver, boolean check) {
        TupleFactory fac = frame.getFactory();
        Solution sol = null;
        Iterable<Sig> sigs = frame.getAllReachableSigs();
        if (hasSig(sigs, "this/Book") != null) {
            Tuple B0N0A0 = t_tuple(fac, "Book$0", "Name$0", "Addr$0");
            Tuple B0N1A0 = t_tuple(fac, "Book$0", "Name$1", "Addr$0");
            Tuple B0N2A0 = t_tuple(fac, "Book$0", "Name$2", "Addr$0");
            Tuple B0N2A1 = t_tuple(fac, "Book$0", "Name$2", "Addr$1");
            Tuple B0N1A1 = t_tuple(fac, "Book$0", "Name$1", "Addr$1");
            Tuple B1N0A0 = t_tuple(fac, "Book$1", "Name$0", "Addr$0");
            Tuple B1N2A1 = t_tuple(fac, "Book$1", "Name$2", "Addr$1");
            Tuple B1N1A1 = t_tuple(fac, "Book$1", "Name$1", "Addr$1");
            Tuple B000 = t_tuple(fac, "Book$0", "Target$0", "Target$0");
            Tuple B001 = t_tuple(fac, "Book$0", "Target$0", "Target$1");
            Tuple B002 = t_tuple(fac, "Book$0", "Target$0", "Target$2");
            Tuple B010 = t_tuple(fac, "Book$0", "Target$1", "Target$0");
            Tuple B101 = t_tuple(fac, "Book$1", "Target$0", "Target$1");
            Tuple B110 = t_tuple(fac, "Book$1", "Target$1", "Target$0");
            Tuple B102 = t_tuple(fac, "Book$1", "Target$0", "Target$2");
            Tuple B210 = t_tuple(fac, "Book$2", "Target$1", "Target$0");
            Tuple B202 = t_tuple(fac, "Book$2", "Target$0", "Target$2");
            Tuple B212 = t_tuple(fac, "Book$2", "Target$1", "Target$2");
            Tuple B302 = t_tuple(fac, "Book$3", "Target$0", "Target$2");
            Tuple B310 = t_tuple(fac, "Book$3", "Target$1", "Target$0");
            Tuple B312 = t_tuple(fac, "Book$3", "Target$1", "Target$2");
            if (sol == null && B000 != null)
                sol = trial(rep, fac, solver, sigs, formula, frame, new Object[] {
                                                                                  "Fig 2.9", "Book$0", "", "this/Book", "", "Target$0", "", "this/Alias", "", "", "this/Group", "", "", "this/Addr", "", B000, "", "this/Book", "addr",
                });
            if (sol == null && B001 != null)
                sol = trial(rep, fac, solver, sigs, formula, frame, new Object[] {
                                                                                  "Fig 2.10", "Book$0", "", "this/Book", "", "", "this/Alias", "", "Target$0", "", "this/Group", "", "Target$1", "Target$2", "", "this/Addr", "", B001, B002, "", "this/Book", "addr",
                });
            if (sol == null && B001 != null)
                sol = trial(rep, fac, solver, sigs, formula, frame, new Object[] {
                                                                                  "Fig 2.11", "Book$0", "", "this/Book", "", "Target$0", "", "this/Alias", "", "", "this/Group", "", "Target$1", "Target$2", "", "this/Addr", "", B001, B002, "", "this/Book", "addr",
                });
            if (sol == null && B001 != null)
                sol = trial(rep, fac, solver, sigs, formula, frame, new Object[] {
                                                                                  "Fig 2.12", "Book$0", "", "this/Book", "", "Target$0", "", "this/Alias", "", "Target$1", "", "this/Group", "", "", "this/Addr", "", B001, "", "this/Book", "addr",
                });
            if (sol == null && B010 != null)
                sol = trial(rep, fac, solver, sigs, formula, frame, new Object[] {
                                                                                  "Fig 2.13", "Book$0", "Book$1", "", "this/Book", "", "", "this/Alias", "", "Target$0", "Target$1", "", "this/Group", "", "Target$2", "", "this/Addr", "", B010, B110, B102, "", "this/Book", "addr",
                });
            if (sol == null && B312 != null)
                sol = trial(rep, fac, solver, sigs, formula, frame, new Object[] {
                                                                                  "Fig 2.15", "Book$0", "Book$1", "Book$2", "Book$3", "", "this/Book", "", "", "this/Alias", "", "Target$0", "Target$1", "", "this/Group", "", "Target$2", "", "this/Addr", "", B102, B210, B202, B212, B302, B312, "", "this/Book", "addr",
                });
            if (sol == null && B101 != null)
                sol = trial(rep, fac, solver, sigs, formula, frame, new Object[] {
                                                                                  "Fig 2.16", "Book$0", "Book$1", "Book$2", "Book$3", "", "this/Book", "", "Target$1", "", "this/Alias", "", "Target$0", "", "this/Group", "", "", "this/Addr", "", B101, "", "this/Book", "addr",
                });
            if (sol == null && B102 != null)
                sol = trial(rep, fac, solver, sigs, formula, frame, new Object[] {
                                                                                  "Fig 2.17", "Book$0", "Book$1", "Book$2", "Book$3", "", "this/Book", "", "Target$0", "", "this/Alias", "", "Target$1", "", "this/Group", "", "Target$2", "", "this/Addr", "", B102, B210, B310, B302, "", "this/Book", "addr",
                });
            if (sol == null && B0N0A0 != null && check)
                sol = trial(rep, fac, solver, sigs, formula, frame, new Object[] {
                                                                                  "Fig 2.6", "Book$0", "Book$1", "", "this/Book", "", "Addr$0", "", "this/Addr", "", "Name$0", "", "this/Name", "", B0N0A0, "", "this/Book", "addr",
                });
            if (sol == null && B1N0A0 != null && !check)
                sol = trial(rep, fac, solver, sigs, formula, frame, new Object[] {
                                                                                  "Fig 2.4", "Book$0", "Book$1", "", "this/Book", "", "Addr$0", "", "this/Addr", "", "Name$0", "", "this/Name", "", B1N0A0, "", "this/Book", "addr",
                });
            if (sol == null && B0N2A1 != null)
                sol = trial(rep, fac, solver, sigs, formula, frame, new Object[] {
                                                                                  "Fig 2.5", "Book$0", "Book$1", "", "this/Book", "", "Addr$0", "Addr$1", "", "this/Addr", "", "Name$0", "Name$1", "Name$2", "", "this/Name", "", B0N2A1, B0N1A1, B1N2A1, B1N1A1, B1N0A0, "", "this/Book", "addr",
                });
            if (sol == null && B0N0A0 != null)
                sol = trial(rep, fac, solver, sigs, formula, frame, new Object[] {
                                                                                  "Fig 2.1", "Book$0", "", "this/Book", "", "Addr$0", "", "this/Addr", "", "Name$0", "", "this/Name", "", B0N0A0, "", "this/Book", "addr",
                });
            if (sol == null && B0N0A0 != null)
                sol = trial(rep, fac, solver, sigs, formula, frame, new Object[] {
                                                                                  "Fig 2.2", "Book$0", "", "this/Book", "", "Addr$0", "", "this/Addr", "", "Name$0", "Name$1", "Name$2", "", "this/Name", "", B0N0A0, B0N1A0, B0N2A0, "", "this/Book", "addr",
                });
            if (sol == null && B0N0A0 != null)
                sol = trial(rep, fac, solver, sigs, formula, frame, new Object[] {
                                                                                  "Fig 2.3", "Book$0", "", "this/Book", "", "Addr$0", "Addr$1", "", "this/Addr", "", "Name$0", "Name$1", "Name$2", "", "this/Name", "", B0N0A0, B0N1A0, B0N2A1, "", "this/Book", "addr",
                });
            if (sol == null && B001 != null)
                sol = trial(rep, fac, solver, sigs, formula, frame, new Object[] {
                                                                                  "Fig 5.2", "Book$0", "Book$1", "", "this/Book", "", "Target$0", "", "this/Name", "", "Target$1", "", "this/Addr", "", B001, B101, "", "this/Book", "addr",
                });
            if (sol == null && B102 != null)
                sol = trial(rep, fac, solver, sigs, formula, frame, new Object[] {
                                                                                  "Fig 5.3", "Book$0", "Book$1", "", "this/Book", "", "Target$0", "Target$1", "", "this/Name", "", "Target$2", "", "this/Addr", "", B010, B110, B102, "", "this/Book", "addr",
                });
        } else if (hasSig(sigs, "this/Woman") != null) {
            Tuple man0_woman0 = t_tuple(fac, "Person$1", "Person$0");
            Tuple man1_woman0 = t_tuple(fac, "Person$2", "Person$0");
            Tuple man0_woman1 = t_tuple(fac, "Person$1", "Person$3");
            Tuple man1_woman1 = t_tuple(fac, "Person$2", "Person$3");
            if (sol == null)
                sol = trial(rep, fac, solver, sigs, formula, frame, new Object[] {
                                                                                  "Fig 4.2", "Person$1", "", "this/Man", "", "Person$0", "", "this/Woman", "", man0_woman0, "", "this/Man", "wife", man0_woman0, "", "this/Person", "mother", "", "this/Person", "father",
                });
            if (sol == null)
                sol = trial(rep, fac, solver, sigs, formula, frame, new Object[] {
                                                                                  "Fig 4.3", "Person$1", "Person$2", "", "this/Man", "", "Person$0", "Person$3", "", "this/Woman", "", man1_woman0, man0_woman1, "", "this/Man", "wife", man1_woman1, man0_woman0, "", "this/Person", "mother", "", "this/Person", "father",
                });
        } else if (hasSig(sigs, "this/Process") != null) {
            String p0 = "Process$0", p1 = "Process$1", p2 = "Process$2";
            String t0 = "Time$0", t1 = "Time$1", t2 = "Time$2", t3 = "Time$3";
            Tuple s20 = t_tuple(fac, p2, p0), s01 = t_tuple(fac, p0, p1), s12 = t_tuple(fac, p1, p2);
            Tuple d000 = t_tuple(fac, p0, p0, t0), d110 = t_tuple(fac, p1, p1, t0), d220 = t_tuple(fac, p2, p2, t0);
            Tuple d001 = t_tuple(fac, p0, p0, t1), d021 = t_tuple(fac, p0, p2, t1), d111 = t_tuple(fac, p1, p1, t1);
            Tuple d002 = t_tuple(fac, p0, p0, t2), d112 = t_tuple(fac, p1, p1, t2), d122 = t_tuple(fac, p1, p2, t2);
            Tuple d003 = t_tuple(fac, p0, p0, t3), d113 = t_tuple(fac, p1, p1, t3), d223 = t_tuple(fac, p2, p2, t3);
            if (sol == null && d000 != null)
                sol = trial(rep, fac, solver, sigs, formula, frame, new Object[] {
                                                                                  "Fig 6.4", s20, s01, s12, "", "this/Process", "succ", d000, d110, d220, d001, d021, d111, d002, d112, d122, d003, d113, d223, "", "this/Process", "toSend", t_tuple(fac, p2, t3), "", "this/Process", "elected",
                });
        } else if (hasSig(sigs, "this/Desk") != null) {
            String g0 = "Guest$0", g1 = "Guest$1", r = "Room$0", k0 = "Key$0", k1 = "Key$1";
            String t0 = "Time$0", t1 = "Time$1", t2 = "Time$2", t3 = "Time$3", t4 = "Time$4", t5 = "Time$5";
            String c0 = "Card$0", c1 = "Card$1";
            if (sol == null)
                sol = trial(rep, fac, solver, sigs, formula, frame, new Object[] {
                                                                                  "Fig E.3", t_tuple(fac, c0, k0), t_tuple(fac, c1, k1), "", "this/Card", "fst", t_tuple(fac, c0, k1), t_tuple(fac, c1, k0), "", "this/Card", "snd", t_tuple(fac, g0, c0, t1), t_tuple(fac, g0, c0, t2), t_tuple(fac, g1, c1, t2), t_tuple(fac, g0, c0, t3), t_tuple(fac, g1, c1, t3), t_tuple(fac, g0, c0, t4), t_tuple(fac, g1, c1, t4), t_tuple(fac, g0, c0, t5), t_tuple(fac, g1, c1, t5), "", "this/Guest", "cards", t_tuple(fac, r, k0, t0), t_tuple(fac, r, k0, t1), t_tuple(fac, r, k0, t2), t_tuple(fac, r, k1, t3), t_tuple(fac, r, k0, t4), t_tuple(fac, r, k1, t5), "", "this/Room", "key", t_tuple(fac, k1, t1), t_tuple(fac, k0, t2), t_tuple(fac, k1, t2), t_tuple(fac, k0, t3), t_tuple(fac, k1, t3), t_tuple(fac, k0, t4), t_tuple(fac, k1, t4), t_tuple(fac, k0, t5), t_tuple(fac, k1, t5), "", "this/Desk", "issued", t_tuple(fac, r, k0, t0), t_tuple(fac, r, k1, t1), t_tuple(fac, r, k0, t2), t_tuple(fac, r, k0, t3), t_tuple(fac, r, k0, t4), t_tuple(fac, r, k0, t5), "", "this/Desk", "prev"
                });
        } else if (hasSig(sigs, "this/FrontDesk") != null) {
            String g0 = "Guest$0", g1 = "Guest$1", r = "Room$0", k0 = "Key$0", k1 = "Key$1", k2 = "Key$2";
            String t0 = "Time$0", t1 = "Time$1", t2 = "Time$2", t3 = "Time$3", t4 = "Time$4";
            Tuple G0 = t_tuple(fac, g0), G1 = t_tuple(fac, g1);
            Tuple K0 = t_tuple(fac, r, k0), K1 = t_tuple(fac, r, k1), K2 = t_tuple(fac, r, k2);
            Tuple K0T0 = t_tuple(fac, r, k0, t0), K0T1 = t_tuple(fac, r, k0, t1), K0T2 = t_tuple(fac, r, k0, t2);
            Tuple K0T3 = t_tuple(fac, r, k0, t3), K1T4 = t_tuple(fac, r, k1, t4);
            Tuple F1 = t_tuple(fac, r, k0, t0), F2 = t_tuple(fac, r, k1, t1), F3 = t_tuple(fac, r, k1, t2);
            Tuple F4 = t_tuple(fac, r, k2, t3), F5 = t_tuple(fac, r, k2, t4);
            Tuple GK1 = t_tuple(fac, g0, k1, t1), GK2 = t_tuple(fac, g0, k1, t2), GK3 = t_tuple(fac, g0, k1, t3);
            Tuple GK4 = t_tuple(fac, g1, k2, t3), GK5 = t_tuple(fac, g0, k1, t4), GK6 = t_tuple(fac, g1, k2, t4);
            Tuple O1 = t_tuple(fac, r, g0, t1), O2 = t_tuple(fac, r, g1, t3), O3 = t_tuple(fac, r, g1, t4);
            if (sol == null && K0T0 != null)
                sol = trial(rep, fac, solver, sigs, formula, frame, new Object[] {
                                                                                  "Fig 6.13", G0, G1, "", "this/Guest", "", K0, K1, K2, "", "this/Room", "keys", K0T0, K0T1, K0T2, K0T3, K1T4, "", "this/Room", "currentKey", F1, F2, F3, F4, F5, "", "this/FrontDesk", "lastKey", GK1, GK2, GK3, GK4, GK5, GK6, "", "this/Guest", "keys", O1, O2, O3, "", "this/FrontDesk", "occupant", "Event$0", "Event$1", "", "this/Checkin", "", "Event$2", "", "this/Checkout", "", "Event$3", "", "this/Entry", "", t_tuple(fac, "Event$0", t0), t_tuple(fac, "Event$2", t1), t_tuple(fac, "Event$1", t2), t_tuple(fac, "Event$3", t3), "", "this/Event", "pre",
                });
            if (sol == null && K0T0 != null)
                sol = trial(rep, fac, solver, sigs, formula, frame, new Object[] {
                                                                                  "Fig 6.6", G0, G1, "", "this/Guest", "", K0, K1, K2, "", "this/Room", "keys", K0T0, K0T1, K0T2, K0T3, K1T4, "", "this/Room", "currentKey", F1, F2, F3, F4, F5, "", "this/FrontDesk", "lastKey", GK1, GK2, GK3, GK4, GK5, GK6, "", "this/Guest", "keys", O1, O2, O3, "", "this/FrontDesk", "occupant",
                });
        }
        return sol;
    }

    /** This tries a particular solution against the formula. */
    private static Solution trial(A4Reporter rep, TupleFactory fac, Solver solver, Iterable<Sig> sigs, Formula f, A4Solution frame, Object[] t) {
        try {
            frame.kr2typeCLEAR();
            Bounds b = null;
            TupleSet ts = null;
            for (int i = 1; i < t.length; i++) {
                Object x = t[i];
                if (x == null)
                    return null;
                if (x instanceof String && ((String) x).length() > 0) { // This
                                                                       // means
                                                                       // it's
                                                                       // a
                                                                       // unary
                                                                       // Tuple
                                                                       // containing
                                                                       // the
                                                                       // given
                                                                       // atom
                    Tuple xx = fac.tuple((String) x);
                    if (ts == null)
                        ts = fac.noneOf(1);
                    ts.add(xx);
                    continue;
                }
                if (x instanceof Tuple) { // This means it's a Tuple
                    Tuple xx = (Tuple) x;
                    if (ts == null)
                        ts = fac.noneOf(xx.arity());
                    ts.add(xx);
                    continue;
                }
                if (x instanceof String) { // The empty string means the sig
                                          // name follows here
                    i++;
                    if (i >= t.length - 1 || !(t[i] instanceof String) || !(t[i + 1] instanceof String))
                        return null;
                    String sigName = (String) (t[i]);
                    i++;
                    String fieldName = (String) (t[i]);
                    Sig first = hasSig(sigs, sigName);
                    if (first == null)
                        return null;
                    Expression expr = null;
                    if (fieldName.length() == 0) {
                        expr = frame.a2k(first);
                    } else {
                        for (Field field : first.getFields())
                            if (field.label.equals(fieldName)) {
                                expr = frame.a2k(field);
                                while (expr instanceof BinaryExpression)
                                    expr = ((BinaryExpression) expr).right();
                                break;
                            }
                    }
                    if (!(expr instanceof Relation))
                        return null;
                    if (b == null)
                        b = frame.getBounds(); // We delay the expansive
                                              // Bounds.clone() until we
                                              // really find a possible match
                    if (ts == null)
                        ts = fac.noneOf(expr.arity());
                    if (!ts.containsAll(b.lowerBound((Relation) expr)))
                        return null; // Sanity check
                    if (!b.upperBound((Relation) expr).containsAll(ts))
                        return null; // Sanity check
                    b.boundExactly((Relation) expr, ts);
                    ts = null;
                    continue;
                }
            }
            SATFactory sat = solver.options().solver();
            Solution sol;
            try {
                solver.options().setSolver(SATFactory.DefaultSAT4J);
                sol = solver.solve(f, b);
            } finally {
                solver.options().setSolver(sat);
            }
            if (sol == null || (sol.outcome() != SATISFIABLE && sol.outcome() != TRIVIALLY_SATISFIABLE))
                return null;
            if (rep != null)
                rep.debug("Comment: " + t[0] + "\n");
            return sol;
        } catch (Throwable ex) {
            return null;
        }
    }

    /**
     * This constructs a Kodkod Tuple from the list of atoms, and returns null if no
     * such Tuple can be constructed.
     */
    private static Tuple t_tuple(TupleFactory factory, Object... atoms) {
        try {
            if (atoms.length <= 0)
                return null;
            return factory.tuple(atoms);
        } catch (Throwable ex) {
            return null;
        }
    }
}
