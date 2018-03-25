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

import java.util.Iterator;
import java.util.List;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.MailBug;
import kodkod.ast.BinaryExpression;
import kodkod.ast.BinaryFormula;
import kodkod.ast.ComparisonFormula;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.NaryFormula;
import kodkod.ast.Relation;
import kodkod.ast.operator.ExprCompOperator;
import kodkod.ast.operator.ExprOperator;
import kodkod.ast.operator.FormulaOperator;
import kodkod.instance.TupleSet;

/**
 * Immutable; this class shrinks the unknowns as much as possible in order to
 * reduce the number of variables in final CNF.
 * <p>
 * Currently it recognizes the following patterns:
 * <p>
 * (1) When it sees "A in B", it will try to derive a safe upperbound for B, and
 * then remove any excess unknowns from A's upperbound.
 * <p>
 * (2) When it sees "A = B", it will try to simplify A assuming "A in B", and
 * then simplify B assuming "B in A".
 */

public class Simplifier {

    /** Reporter for receiving debug messages. */
    private A4Reporter rep = null;

    /** The A4Solution object we are attempting to simplify. */
    private A4Solution sol = null;

    /** Construct a Simplifier object. */
    public Simplifier() {}

    /* Stores the equivalence relation discovered so far. */
    // private final IdentityHashMap<Node,List<Expression>> equiv = new
    // IdentityHashMap<Node,List<Expression>>();

    /**
     * Simplify sol.bounds() based on the set of formulas, or to modify the formulas
     * list itself. Subclasses should override this method to implement different
     * simplification algorithms. (Note: this method is allowed to modify the
     * "formulas" array if it sees an opportunity for optimization)
     */
    public boolean simplify(A4Reporter rep, A4Solution sol, List<Formula> formulas) throws Err {
        this.rep = rep;
        this.sol = sol;
        while (true) {
            // equiv.clear();
            for (Formula f : formulas)
                if (!simplify_eq(f))
                    return false;
            for (Formula f : formulas)
                if (!simplify_in(f))
                    return false;
            /*
             * if (equiv.size()==0) return true; // We have to construct this replacer from
             * scratch, since each time it will retain some info we don't want final
             * AbstractReplacer ar = new AbstractReplacer(new
             * kodkod.util.collections.IdentityHashSet<Node>()) {
             * @Override public Expression visit(Relation relation) { List<Expression> list
             * = equiv.get(relation); if (list!=null) return list.get(0); else return
             * relation; } }; for(Map.Entry<Node,List<Expression>> e: equiv.entrySet())
             * System.out.println("Equiv: "+e); System.out.flush(); for(int
             * i=formulas.size()-1; i>=0; i--) { Formula OLD = formulas.get(i); Formula NEW
             * = OLD.accept(ar); if (OLD!=NEW) {
             * System.out.println("OLD->NEW: "+OLD+" ===> "+NEW); System.out.flush(); }
             * formulas.set(i, NEW); }
             */
            return true;
        }
    }

    /**
     * Simplify (a.(a->b)) into b when semantically equivalent
     */
    private final Expression condense(Expression x) {
        while (x instanceof BinaryExpression) {
            BinaryExpression b = (BinaryExpression) x;
            if (b.op() == ExprOperator.JOIN && b.left() instanceof Relation && b.right() instanceof BinaryExpression) {
                Relation r = (Relation) (b.left());
                try {
                    if (sol.query(true, r, false).size() != 1)
                        return x;
                    if (sol.query(false, r, false).size() != 1)
                        return x;
                } catch (Err er) {
                    return x;
                }
                b = (BinaryExpression) (b.right());
                if (b.op() == ExprOperator.PRODUCT && b.left() == r) {
                    x = b.right();
                    continue;
                }
            }
            break;
        }
        return x;
    }

    /**
     * Simplify the bounds based on the fact that "a == b"; return false if we
     * discover the formula is unsat.
     */
    private final boolean simplify_equal(Expression a, Expression b) {
        a = condense(a);
        b = condense(b);
        /*
         * System.out.println("A: "+a+" B: "+b); System.out.flush(); if (a instanceof
         * Relation && b instanceof Relation && a!=b) { List<Expression> al =
         * equiv.get(a); List<Expression> bl = equiv.get(b); if (al==null) { Expression
         * oldA=a; al=bl; bl=null; a=b; b=oldA; } if (al==null) { al = new
         * ArrayList<Expression>(); al.add(a); al.add(b); equiv.put(a, al); equiv.put(b,
         * al); System.out.println("BothNewEquivalent: "+a+" "+b); System.out.flush(); }
         * else if (bl==null) { al.add(b); equiv.put(b, al);
         * System.out.println("NewEquivalent: "+a+" "+b); System.out.flush(); } else if
         * (al!=bl) { al.addAll(bl); for(Node x: bl) equiv.put(x, al);
         * System.out.println("MergeEquivalent: "+a+" "+b); System.out.flush(); } } else
         */
        if (a instanceof Relation || b instanceof Relation) {
            try {
                TupleSet a0 = sol.query(false, a, false), a1 = sol.query(true, a, false);
                TupleSet b0 = sol.query(false, b, false), b1 = sol.query(true, b, false);
                if (a instanceof Relation && a0.size() < b0.size() && b0.containsAll(a0) && a1.containsAll(b0)) {
                    rep.debug("Comment: Simplify " + a + " " + (a1.size() - a0.size()) + "->" + (a1.size() - b0.size()) + "\n");
                    sol.shrink((Relation) a, a0 = b0, a1);
                }
                if (a instanceof Relation && a1.size() > b1.size() && b1.containsAll(a0) && a1.containsAll(b1)) {
                    rep.debug("Comment: Simplify " + a + " " + (a1.size() - a0.size()) + "->" + (b1.size() - a0.size()) + "\n");
                    sol.shrink((Relation) a, a0, a1 = b1);
                }
                if (b instanceof Relation && b0.size() < a0.size() && a0.containsAll(b0) && b1.containsAll(a0)) {
                    rep.debug("Comment: Simplify " + b + " " + (b1.size() - b0.size()) + "->" + (b1.size() - a0.size()) + "\n");
                    sol.shrink((Relation) b, b0 = a0, b1);
                }
                if (b instanceof Relation && b1.size() > a1.size() && a1.containsAll(b0) && b1.containsAll(a1)) {
                    rep.debug("Comment: Simplify " + b + " " + (b1.size() - b0.size()) + "->" + (a1.size() - b0.size()) + "\n");
                    sol.shrink((Relation) b, b0, b1 = a1);
                }
            } catch (Exception ex) {}
        }
        return true;
    }

    /**
     * Simplify the bounds based on the fact that "a is subset of b"; return false
     * if we discover the formula is unsat.
     */
    private final boolean simplify_in(Expression a, Expression b) {
        a = condense(a);
        b = condense(b);
        if (a instanceof Relation) {
            try {
                Relation r = (Relation) a;
                TupleSet ub = sol.query(true, r, false), lb = sol.query(false, r, false), t = sol.approximate(b);
                t.retainAll(ub);
                if (!t.containsAll(lb)) {
                    rep.debug("Comment: Simplify " + a + " " + ub.size() + "->false\n");
                    return false;
                } // This means the upperbound is shrunk BELOW the lowerbound.
                if (t.size() < ub.size()) {
                    rep.debug("Comment: Simplify " + a + " " + ub.size() + "->" + t.size() + "\n");
                    sol.shrink(r, lb, t);
                }
            } catch (Throwable ex) {
                rep.debug("Comment: Simplify " + a + " exception: " + ex + "\n" + MailBug.dump(ex).trim() + "\n"); // Not
                                                                                                                  // fatal;
                                                                                                                  // let's
                                                                                                                  // report
                                                                                                                  // it
                                                                                                                  // to
                                                                                                                  // the
                                                                                                                  // debug()
                                                                                                                  // reporter
            }
        }
        return true;
    }

    // ALTERNATIVE VERSION THAT COMPUTES LOWER BOUNDS AS WELL
    // /** Simplify the bounds based on the fact that "a is subset of b"; return
    // false if we discover the formula is unsat. */
    // private final boolean simplify_in(Expression a, Expression b) {
    // a = condense(a);
    // b = condense(b);
    // if (a instanceof Relation) {
    // return simpIn((Relation)a, b, true);
    // }
    // if (b instanceof Relation) {
    // return simpIn((Relation)b, a, false);
    // }
    // return true;
    // }
    //
    // private final boolean simpIn(Relation r, Expression b, boolean bIsUpper)
    // {
    // try {
    // TupleSet ub = sol.query(true, r, false);
    // TupleSet lb = sol.query(false, r, false);
    // TupleSet t = sol.approximate(b);
    // t.retainAll(ub);
    // if (bIsUpper) {
    // if (!t.containsAll(lb)) {
    // // This means the upperbound is shrunk BELOW the lowerbound.
    // rep.debug("Comment: Simplify upper "+r+" "+ub.size()+"->false\n");
    // return false;
    // }
    // if (t.size() < ub.size()) {
    // rep.debug("Comment: Simplify upper "+r+" "+ub.size()+"->"+t.size()+"\n");
    // sol.shrink(r,lb,t);
    // }
    // } else {
    // if (!ub.containsAll(t)) {
    // // This means the upperbound is shrunk BELOW the lowerbound.
    // rep.debug("Comment: Simplify lower "+r+" "+lb.size()+"->false\n");
    // return false;
    // }
    // if (lb.size() < t.size()) {
    // rep.debug("Comment: Simplify lower "+r+" "+lb.size()+"->"+t.size()+"\n");
    // sol.shrink(r,t,ub);
    // }
    // }
    // } catch(Throwable ex) {
    // rep.debug("Comment: Simplify "+r+" exception:
    // "+ex+"\n"+MailBug.dump(ex).trim()+"\n"); // Not fatal; let's report it to
    // the debug() reporter
    // }
    // return true;
    // }

    /**
     * Simplify the bounds based on the fact that "form is true"; return false if we
     * discover the formula is unsat.
     */
    private final boolean simplify_in(Formula form) {
        if (form instanceof NaryFormula) {
            NaryFormula f = (NaryFormula) form;
            if (f.op() == FormulaOperator.AND) {
                for (Iterator<Formula> i = f.iterator(); i.hasNext();)
                    if (!simplify_in(i.next()))
                        return false;
            }
        }
        if (form instanceof BinaryFormula) {
            BinaryFormula f = (BinaryFormula) form;
            if (f.op() == FormulaOperator.AND) {
                return simplify_in(f.left()) && simplify_in(f.right());
            }
        }
        if (form instanceof ComparisonFormula) {
            ComparisonFormula f = (ComparisonFormula) form;
            if (f.op() == ExprCompOperator.SUBSET) {
                if (!simplify_in(f.left(), f.right()))
                    return false;
            }
            if (f.op() == ExprCompOperator.EQUALS) {
                if (!simplify_in(f.left(), f.right()))
                    return false;
                if (!simplify_in(f.right(), f.left()))
                    return false;
            }
        }
        return true;
    }

    /**
     * Simplify the bounds based on the fact that "form is true"; return false if we
     * discover the formula is unsat.
     */
    private final boolean simplify_eq(Formula form) {
        if (form instanceof NaryFormula) {
            NaryFormula f = (NaryFormula) form;
            if (f.op() == FormulaOperator.AND) {
                for (Iterator<Formula> i = f.iterator(); i.hasNext();)
                    if (!simplify_eq(i.next()))
                        return false;
            }
        }
        if (form instanceof BinaryFormula) {
            BinaryFormula f = (BinaryFormula) form;
            if (f.op() == FormulaOperator.AND) {
                return simplify_eq(f.left()) && simplify_eq(f.right());
            }
        }
        if (form instanceof ComparisonFormula) {
            ComparisonFormula f = (ComparisonFormula) form;
            if (f.op() == ExprCompOperator.EQUALS) {
                if (!simplify_equal(f.left(), f.right()))
                    return false;
            }
        }
        return true;
    }
}
