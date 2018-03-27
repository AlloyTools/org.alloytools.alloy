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

package edu.mit.csail.sdg.alloy4viz;

import static edu.mit.csail.sdg.alloy4.Util.encode;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.OurTree;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.A4Tuple;
import edu.mit.csail.sdg.translator.A4TupleSet;

/**
 * GUI tree that displays an instance as a tree.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

public final class VizTree extends OurTree {

    /** {@inheritDoc} */
    @Override
    public String convertValueToText(Object val, boolean selected, boolean expanded, boolean leaf, int row, boolean focus) {
        String c = ">";
        if (onWindows)
            c = selected ? " style=\"color:#ffffff;\">" : " style=\"color:#000000;\">";
        if (val instanceof A4Solution)
            return "<html> <b" + c + encode(title == null ? "" : title) + "</b></html>";
        if (val instanceof Sig) {
            String label = ((Sig) val).label;
            if (label.startsWith("this/"))
                label = label.substring(5);
            return "<html> <b" + c + "sig " + encode(label) + "</b></html>";
        }
        if (val instanceof ExprVar)
            return "<html> <b" + c + "set " + encode(((ExprVar) val).label) + "</b></html>";
        if (val instanceof String)
            return "<html> <span" + c + encode((String) val) + "</span></html>";
        if (val instanceof Pair)
            return "<html> <b" + c + "field " + encode(((ExprHasName) (((Pair< ? , ? >) val).b)).label) + "</b></html>";
        if (val instanceof A4Tuple) {
            StringBuilder sb = new StringBuilder("<html> <span" + c);
            A4Tuple tp = (A4Tuple) val;
            for (int i = 1; i < tp.arity(); i++) {
                if (i > 1)
                    sb.append(" -> ");
                sb.append(encode(tp.atom(i)));
            }
            sb.append("</span></html>");
            return sb.toString();
        }
        return "";
    }

    /** {@inheritDoc} */
    @Override
    public Object do_root() {
        return instance;
    }

    /** {@inheritDoc} */
    @Override
    public List< ? > do_ask(Object parent) {
        List<Object> ans = new ArrayList<Object>();
        try {
            if (parent instanceof A4Solution) {
                return toplevel;
            } else if (parent instanceof Sig || parent instanceof ExprVar) {
                A4TupleSet ts = (A4TupleSet) (instance.eval((Expr) parent));
                for (A4Tuple t : ts)
                    ans.add(t.atom(0));
            } else if (parent instanceof String) {
                String atom = (String) parent;
                for (Sig s : instance.getAllReachableSigs())
                    for (Field f : s.getFields())
                        for (A4Tuple t : instance.eval(f)) {
                            if (t.atom(0).equals(atom)) {
                                ans.add(new Pair<String,ExprHasName>(atom, f));
                                break;
                            }
                        }
                for (ExprVar f : instance.getAllSkolems())
                    if (f.type().arity() > 1)
                        for (A4Tuple t : (A4TupleSet) (instance.eval(f))) {
                            if (t.atom(0).equals(atom)) {
                                ans.add(new Pair<String,ExprHasName>(atom, f));
                                break;
                            }
                        }
            } else if (parent instanceof Pair) {
                Pair< ? , ? > p = (Pair< ? , ? >) parent;
                ExprHasName rel = (ExprHasName) (p.b);
                String atom = (String) (p.a);
                for (A4Tuple tuple : (A4TupleSet) (instance.eval(rel)))
                    if (tuple.atom(0).equals(atom)) {
                        if (tuple.arity() == 2)
                            ans.add(tuple.atom(1));
                        else
                            ans.add(tuple);
                    }
            } else if (parent instanceof A4Tuple) {
                A4Tuple tp = (A4Tuple) parent;
                for (int i = 1; i < tp.arity(); i++)
                    if (!ans.contains(tp.atom(i)))
                        ans.add(tp.atom(i));
                return ans; // we don't want to sort this; we want the original
                           // order
            }
            Collections.sort(ans, new Comparator<Object>() {

                @Override
                public int compare(Object a, Object b) {
                    String t1, t2;
                    if (a instanceof Pair) {
                        t1 = ((ExprHasName) (((Pair< ? , ? >) a).b)).label;
                        t2 = ((ExprHasName) (((Pair< ? , ? >) b).b)).label;
                    } else {
                        t1 = a.toString();
                        t2 = b.toString();
                    }
                    int i = t1.compareToIgnoreCase(t2);
                    if (i != 0)
                        return i;
                    else
                        return t1.compareTo(t2);
                }
            });
            return ans;
        } catch (Err er) {
            return ans;
        }
    }

    /** This ensures the class can be serialized reliably. */
    private static final long  serialVersionUID = 0;

    /** Caches whether we're on Windows or not. */
    private final boolean      onWindows;

    /** The title of this tree. */
    private final String       title;

    /** The instance being displayed. */
    private final A4Solution   instance;

    /** The list of toplevel nodes to show. */
    private final List<Object> toplevel;

    /** Constructs a tree to display the given instance. */
    public VizTree(A4Solution instance, String title, int fontSize) {
        super(fontSize);
        this.instance = instance;
        this.title = title;
        this.onWindows = Util.onWindows();
        ArrayList<Object> toplevel = new ArrayList<Object>();
        for (Sig s : instance.getAllReachableSigs())
            if (s != Sig.UNIV && s != Sig.SEQIDX && s != Sig.NONE)
                toplevel.add(s);
        for (ExprVar v : instance.getAllSkolems())
            if (v.type().arity() == 1 && v.label.startsWith("$"))
                toplevel.add(v);
        Collections.sort(toplevel, new Comparator<Object>() {

            @Override
            public int compare(Object a, Object b) {
                String t1, t2;
                if (a instanceof Sig) {
                    t1 = ((Sig) a).label;
                    if (b instanceof ExprVar)
                        return -1;
                    else
                        t2 = ((Sig) b).label;
                } else {
                    t1 = ((ExprVar) a).label;
                    if (b instanceof Sig)
                        return 1;
                    else
                        t2 = ((ExprVar) b).label;
                }
                return Util.slashComparator.compare(t1, t2);
            }
        });
        this.toplevel = Collections.unmodifiableList(toplevel);
        do_start();
    }
}
