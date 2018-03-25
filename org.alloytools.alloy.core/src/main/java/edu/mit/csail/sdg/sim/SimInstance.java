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

package edu.mit.csail.sdg.sim;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import edu.mit.csail.sdg.alloy4.ConstList.TempList;
import edu.mit.csail.sdg.alloy4.Env;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorAPI;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Sig.PrimSig;
import edu.mit.csail.sdg.ast.Sig.SubsetSig;
import edu.mit.csail.sdg.ast.VisitReturn;

/** Mutable; represents an instance. */

public final class SimInstance extends VisitReturn<Object> {

    /** The root module associated with this instance. */
    public final Module                 root;

    /**
     * This maps the current local variables (LET, QUANT, Function Param) to the
     * actual SimTupleset/Integer/Boolean
     */
    private Env<ExprVar,Object>         env               = new Env<ExprVar,Object>();

    /**
     * This stores the "call backs" where you can supply Java code to efficiently
     * handle certain functions/predicates.
     */
    private final Map<Func,SimCallback> callbacks;

    /**
     * The exact values of each sig, field, and skolem (Note: it must not cache the
     * value of any "defined" field, nor any builtin sig)
     */
    private final Map<Expr,SimTupleset> sfs               = new LinkedHashMap<Expr,SimTupleset>();

    /**
     * If nonnull, it caches the current value of STRING (this value must be cleared
     * or updated when you change the value of sigs/fields/vars)
     */
    private SimTupleset                 cacheSTRING       = null;

    /**
     * If nonnull, it caches the current value of UNIV (this value must be cleared
     * or updated when you change the value of sigs)
     */
    private SimTupleset                 cacheUNIV         = null;

    /**
     * Caches parameter-less functions to a Boolean, Integer, or SimTupleset.
     */
    private final Map<Func,Object>      cacheForConstants = new IdentityHashMap<Func,Object>();

    /**
     * This is used to detect "function recursion" (which we currently do not
     * allow).
     */
    private final List<Func>            current_function  = new ArrayList<Func>();

    /** The chosen bitwidth */
    private final int                   bitwidth;

    /** The chosen maxseq length. */
    private final int                   maxseq;

    /** The shiftmask based on the chosen bitwidth. */
    private final int                   shiftmask;

    /**
     * The minimum allowed integer based on the chosen bitwidth.
     */
    private final int                   min;

    /**
     * The maximum allowed integer based on the chosen bitwidth.
     */
    private final int                   max;

    /**
     * Whether the was overflow the last time "trunc" was called
     */
    private boolean                     wasOverflow;

    public boolean wasOverflow() {
        return wasOverflow;
    }

    /**
     * Helper method that encodes the given string using UTF-8 and write to the
     * output stream.
     */
    private static void write(BufferedOutputStream out, String string) throws IOException {
        out.write(string.getBytes("UTF-8"));
    }

    /**
     * Write the bitwidth, maxseq, set of all atoms, and map of all sig/field/var
     * into the given file.
     */
    public void write(String filename) throws IOException {
        FileOutputStream fos = null;
        BufferedOutputStream bos = null;
        try {
            fos = new FileOutputStream(filename);
            bos = new BufferedOutputStream(fos);
            write(bos);
            bos.flush();
            bos.close();
            bos = null;
            fos.close();
            fos = null;
        } finally {
            Util.close(bos);
            Util.close(fos);
        }
    }

    /**
     * Write the bitwidth, maxseq, set of all atoms, and map of all sig/field/var
     * into the given file.
     */
    private void write(BufferedOutputStream out) throws IOException {
        write(out, "maxseq = " + maxseq + ("\n" + "bitwidth = ") + bitwidth + "\n");
        for (Map.Entry<Expr,SimTupleset> entry : sfs.entrySet()) {
            Expr e = entry.getKey();
            if (e instanceof Sig)
                write(out, "sig " + ((Sig) e).label + " = ");
            else if (e instanceof Field)
                write(out, "field " + ((Field) e).sig.label + " " + ((Field) e).label + " = ");
            else if (e instanceof ExprVar)
                write(out, "var " + ((ExprVar) e).label + " = ");
            else
                continue;
            entry.getValue().write(out);
            out.write('\n');
        }
    }

    /**
     * Temporary buffer used by the parser; access to this buffer must be
     * synchronized on SimInstance's class.
     */
    private static byte[] readcache = null;

    /**
     * Helper method that read a non-negative integer followed by a line break.
     */
    private static int readNonNegativeIntThenLinebreak(BufferedInputStream bis) throws IOException {
        int n = 0;
        while (true) {
            int c = bis.read();
            if (c < 0)
                throw new IOException("Unexpected EOF");
            if (c == '\n')
                return n;
            if (c > 0 && c <= ' ')
                continue; // skip white space
            if (!(c >= '0' && c <= '9'))
                throw new IOException("Expects a DIGIT or a white space!");
            n = n * 10 + (c - '0');
        }
    }

    /**
     * Helper method that read "key =" then return the key part (with leading and
     * trailing spaces removed). This method can only be called after you've
     * synchronized on SimInstance's class.
     */
    private static String readkey(BufferedInputStream bis) throws IOException {
        int n = 0;
        while (true) {
            int c = bis.read();
            if (c < 0)
                return "";
            if (c == '=')
                break;
            if (readcache == null)
                readcache = new byte[64]; // to ensure proper detection of
                                         // out-of-memory error, this number
                                         // must be 2^n for some n>=0
            while (n >= readcache.length) {
                byte[] readcache2 = new byte[readcache.length * 2];
                System.arraycopy(readcache, 0, readcache2, 0, readcache.length);
                readcache = readcache2;
            }
            readcache[n] = (byte) c;
            n++;
        }
        while (n > 0 && readcache[n - 1] > 0 && readcache[n - 1] <= ' ')
            n--; // skip trailing spaces
        int i = 0;
        while (i < n && readcache[i] > 0 && readcache[i] <= ' ')
            i++; // skip leading space
        return new String(readcache, i, n - i, "UTF-8");
    }

    /**
     * Construct a new simulation context by reading the given file.
     */
    public static synchronized SimInstance read(Module root, String filename, List<ExprVar> vars) throws Err, IOException {
        FileInputStream fis = null;
        BufferedInputStream bis = null;
        try {
            fis = new FileInputStream(filename);
            bis = new BufferedInputStream(fis);
            // read maxseq
            if (!readkey(bis).equals("maxseq"))
                throw new IOException("Expecting maxseq = ...");
            int maxseq = readNonNegativeIntThenLinebreak(bis);
            // read bitwidth
            if (!readkey(bis).equals("bitwidth"))
                throw new IOException("Expecting bitwidth = ...");
            int bitwidth = readNonNegativeIntThenLinebreak(bis);
            // construct the SimInstance object with no atoms and no relations
            SimInstance ans = new SimInstance(root, bitwidth, maxseq);
            // parse all the relations
            Map<String,SimTupleset> sfs = new HashMap<String,SimTupleset>();
            while (true) {
                String key = readkey(bis);
                if (key.length() == 0)
                    break; // we don't expect any more data after this
                sfs.put(key, SimTupleset.read(bis));
            }
            // now for each user-supplied sig, if we saw its value earlier, then
            // assign its value in the new SimInstance's sfs map
            for (final Sig s : root.getAllReachableSigs())
                if (!s.builtin) {
                    SimTupleset ts = sfs.get("sig " + s.label);
                    if (ts != null)
                        ans.sfs.put(s, ts);
                    for (final Field f : s.getFields())
                        if (!f.defined) {
                            ts = sfs.get("field " + s.label + " " + f.label);
                            if (ts != null)
                                ans.sfs.put(f, ts);
                        }
                }
            // now for each user-supplied var, if we saw its value earlier, then
            // assign its value in the new SimInstance's sfs map
            if (vars != null)
                for (ExprVar v : vars) {
                    SimTupleset ts = sfs.get("var " + v.label);
                    if (ts != null)
                        ans.sfs.put(v, ts);
                }
            // close the files then return the answer
            bis.close();
            bis = null;
            fis.close();
            fis = null;
            return ans;
        } finally {
            // free the temporary array
            readcache = null;
            // if an exception occurred, we'll try to close to files anyway,
            // since open file descriptors is a scarce resource
            Util.close(bis);
            Util.close(fis);
        }
    }

    /**
     * Construct a new simulation context with the given bitwidth and the given
     * maximum sequence length.
     */
    public SimInstance(Module root, int bitwidth, int maxseq) throws Err {
        if (bitwidth < 0 || bitwidth > 32)
            throw new ErrorType("Bitwidth must be between 0 and 32.");
        this.root = root;
        this.bitwidth = bitwidth;
        this.maxseq = maxseq;
        this.callbacks = new HashMap<Func,SimCallback>();
        if (bitwidth == 32) {
            max = Integer.MAX_VALUE;
            min = Integer.MIN_VALUE;
        } else {
            max = Util.max(bitwidth);
            min = (0 - max) - 1;
        }
        if (maxseq < 0)
            throw new ErrorSyntax("The maximum sequence length cannot be negative.");
        if (maxseq > 0 && maxseq > max)
            throw new ErrorSyntax("With integer bitwidth of " + bitwidth + ", you cannot have sequence length longer than " + max);
        shiftmask = Util.shiftmask(bitwidth);
    }

    /**
     * Construct a deep copy of this instance (except that it shares the same root
     * Module object as the old instance)
     */
    public SimInstance(SimInstance old) throws Err {
        root = old.root;
        bitwidth = old.bitwidth;
        maxseq = old.maxseq;
        min = old.min;
        max = old.max;
        shiftmask = old.shiftmask;
        env = old.env.dup();
        cacheUNIV = old.cacheUNIV;
        cacheSTRING = old.cacheSTRING;
        callbacks = new HashMap<Func,SimCallback>(old.callbacks);
        for (Map.Entry<Expr,SimTupleset> e : old.sfs.entrySet())
            sfs.put(e.getKey(), e.getValue());
    }

    /** Register a callback. */
    public void addCallback(Func predicateOrFunction, SimCallback callback) {
        callbacks.put(predicateOrFunction, callback);
    }

    /**
     * Returns true if the given atom is an Int atom, or String atom, or is in at
     * least one of the sig.
     */
    public boolean hasAtom(SimAtom atom) {
        if (atom.toString().length() > 0) {
            char c = atom.toString().charAt(0);
            if (c == '-' || (c >= '0' && c <= '9') || c == '\"')
                return true;
        }
        for (Map.Entry<Expr,SimTupleset> e : sfs.entrySet()) {
            if (e.getKey() instanceof PrimSig && ((PrimSig) (e.getKey())).isTopLevel() && e.getValue().has(atom))
                return true;
        }
        return false;
    }

    /**
     * Create a fresh atom for the given sig, then return the newly created atom.
     *
     * @throws ErrorAPI if attempting to add an atom to an abstract sig with
     *             children, or a builtin sig, or a subset sig.
     */
    public SimAtom makeAtom(Sig sig) throws Err {
        if (sig.builtin)
            throw new ErrorAPI("Cannot add an atom to a builtin sig.");
        if (!(sig instanceof PrimSig))
            throw new ErrorAPI("Cannot add an atom to a subset sig.");
        PrimSig s = (PrimSig) sig;
        if (s.isAbstract != null && !s.children().isEmpty())
            throw new ErrorAPI("Cannot add an atom to an abstract parent sig.");
        String label = sig.label + "$";
        if (label.startsWith("this/"))
            label = label.substring(5);
        for (int i = 0;; i++) {
            SimAtom atom = SimAtom.make(label + i);
            if (hasAtom(atom))
                continue;
            SimTupleset add = SimTupleset.make(SimTuple.make(atom));
            if (cacheUNIV != null)
                cacheUNIV = cacheUNIV.union(add);
            for (; s != null; s = s.parent)
                if (!s.builtin) {
                    SimTupleset old = sfs.get(s);
                    if (old == null || old.empty())
                        sfs.put(s, add);
                    else if (!add.in(old))
                        sfs.put(s, old.union(add));
                    else
                        break;
                }
            return atom;
        }
    }

    /**
     * Delete an atom from all sigs/fields/skolem...
     * <p>
     * The resulting instance may or may not satisfy all facts, and should be
     * checked for consistency.
     * <p>
     * Returns true if at least one sig/field/var changed its value as a result of
     * this deletion.
     *
     * @throws ErrorAPI if attempting to delete from "Int".
     */
    public boolean deleteAtom(SimAtom atom) throws Err {
        if (atom.toString().length() > 0) {
            char c = atom.toString().charAt(0);
            if (c == '-' || (c >= '0' && c <= '9') || c == '\"')
                return false;
        }
        boolean changed = false;
        for (Map.Entry<Expr,SimTupleset> x : sfs.entrySet()) {
            SimTupleset oldvalue = x.getValue();
            SimTupleset newvalue = oldvalue.removeAll(atom);
            if (oldvalue.longsize() != newvalue.longsize()) {
                changed = true;
                x.setValue(newvalue);
            }
        }
        if (changed) {
            cacheUNIV = null;
            return true;
        } else {
            return false;
        }
    }

    /**
     * Initializes the given sig to be associated with the given unary value; should
     * only be called at the beginning.
     * <p>
     * The resulting instance may or may not satisfy all facts, and should be
     * checked for consistency.
     */
    public void init(Sig sig, SimTupleset value) throws Err {
        if (value == null) {
            sfs.remove(sig);
            return;
        }
        if (value.arity() > 1)
            throw new ErrorType("Evaluator encountered an error: sig " + sig.label + " arity must not be " + value.arity());
        if (sig.builtin)
            throw new ErrorAPI("Evaluator cannot prebind the builtin sig \"" + sig.label + "\"");
        sfs.put(sig, value);
        cacheUNIV = null;
        cacheSTRING = null;
        cacheForConstants.clear();
    }

    /**
     * Initializes the given field to be associated with the given unary value;
     * should only be called at the beginning.
     * <p>
     * The resulting instance may or may not satisfy all facts, and should be
     * checked for consistency.
     */
    public void init(Field field, SimTupleset value) throws Err {
        if (value == null) {
            sfs.remove(field);
            return;
        }
        if (!value.empty() && value.arity() != field.type().arity())
            throw new ErrorType("Evaluator encountered an error: field " + field.label + " arity must not be " + value.arity());
        if (field.defined)
            throw new ErrorAPI("Evaluator cannot prebind the value of a defined field.");
        sfs.put(field, value);
        cacheUNIV = null;
        cacheSTRING = null;
        cacheForConstants.clear();
    }

    /**
     * Initializes the given var to be associated with the given unary value; should
     * only be called at the beginning.
     * <p>
     * The resulting instance may or may not satisfy all facts, and should be
     * checked for consistency.
     */
    public void init(ExprVar var, SimTupleset value) throws Err {
        if (value == null) {
            sfs.remove(var);
            return;
        }
        if (!value.empty() && value.arity() != var.type().arity())
            throw new ErrorType("Evaluator encountered an error: skolem " + var.label + " arity must not be " + value.arity());
        sfs.put(var, value);
        cacheUNIV = null;
        cacheSTRING = null;
        cacheForConstants.clear();
    }

    /**
     * Truncate the given integer based on the current chosen bitwidth (as string)
     * plus a flag to indicate overflow
     */
    private int trunc(int i) {
        int ret = (i << (32 - bitwidth)) >> (32 - bitwidth);
        wasOverflow = ret != i;
        return ret;
    }

    /**
     * Convenience method that evalutes x and casts the result to be a boolean.
     *
     * @return the boolean - if x evaluates to a boolean
     * @throws ErrorFatal - if x does not evaluate to a boolean
     */
    public boolean cform(Expr x) throws Err {
        if (!x.errors.isEmpty())
            throw x.errors.pick();
        Object y = visitThis(x);
        if (y instanceof Boolean)
            return Boolean.TRUE.equals(y);
        throw new ErrorFatal(x.span(), "This should have been a formula.\nInstead it is " + y);
    }

    /**
     * Convenience method that evalutes x and cast the result to be a int.
     *
     * @return the int - if x evaluates to an int
     * @throws ErrorFatal - if x does not evaluate to an int
     */
    public int cint(Expr x) throws Err {
        if (!x.errors.isEmpty())
            throw x.errors.pick();
        Object y = visitThis(x);
        if (y instanceof Integer)
            return (Integer) y;
        if (y instanceof SimTupleset)
            return ((SimTupleset) y).sum();
        throw new ErrorFatal(x.span(), "This should have been an integer expression.\nInstead it is " + y);
    }

    /**
     * Convenience method that evalutes x and cast the result to be a tupleset
     *
     * @return the tupleset - if x evaluates to a tupleset
     * @throws ErrorFatal - if x does not evaluate to a tupleset
     */
    public SimTupleset cset(Expr x) throws Err {
        if (!x.errors.isEmpty())
            throw x.errors.pick();
        Object y = visitThis(x);
        if (y instanceof SimTupleset)
            return (SimTupleset) y;
        if (y instanceof Integer)
            return SimTupleset.make(SimTuple.make(SimAtom.make(((Integer) y).intValue())));
        throw new ErrorFatal(x.span(), "This should have been a set or a relation.\nInstead it is " + y);
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprBinary x) throws Err {
        Expr a = x.left, b = x.right;
        switch (x.op) {
            case ARROW :
            case ANY_ARROW_LONE :
            case ANY_ARROW_ONE :
            case ANY_ARROW_SOME :
            case LONE_ARROW_ANY :
            case LONE_ARROW_LONE :
            case LONE_ARROW_ONE :
            case LONE_ARROW_SOME :
            case ONE_ARROW_ANY :
            case ONE_ARROW_LONE :
            case ONE_ARROW_ONE :
            case ONE_ARROW_SOME :
            case SOME_ARROW_ANY :
            case SOME_ARROW_LONE :
            case SOME_ARROW_ONE :
            case SOME_ARROW_SOME :
            case ISSEQ_ARROW_LONE :
                return cset(x.left).product(cset(x.right));
            case JOIN :
                if (x.left.isSame(Sig.UNIV)) {
                    SimTupleset tp = cset(x.right);
                    return tp.tail(tp.arity() - 1);
                }
                if (x.right.isSame(Sig.UNIV)) {
                    SimTupleset tp = cset(x.left);
                    return tp.head(tp.arity() - 1);
                }
                return cset(x.left).join(cset(x.right));
            case IMPLIES :
                return !cform(x.left) || cform(x.right);
            case AND :
                return cform(x.left) && cform(x.right);
            case OR :
                return cform(x.left) || cform(x.right);
            case IFF :
                return cform(x.left) == cform(x.right);
            case SHA :
                return trunc(cint(x.left) >> (shiftmask & cint(x.right)));
            case SHR :
                return trunc(cint(x.left) >>> (shiftmask & cint(x.right)));
            case SHL :
                return trunc(cint(x.left) << (shiftmask & cint(x.right)));
            case INTERSECT :
                return cset(x.left).intersect(cset(x.right));
            case GT :
                return cint(x.left) > cint(x.right);
            case GTE :
                return cint(x.left) >= cint(x.right);
            case LT :
                return cint(x.left) < cint(x.right);
            case LTE :
                return cint(x.left) <= cint(x.right);
            case NOT_GT :
                return !(cint(x.left) > cint(x.right));
            case NOT_GTE :
                return !(cint(x.left) >= cint(x.right));
            case NOT_LT :
                return !(cint(x.left) < cint(x.right));
            case NOT_LTE :
                return !(cint(x.left) <= cint(x.right));
            case DOMAIN :
                return cset(x.left).domain(cset(x.right));
            case RANGE :
                return cset(x.left).range(cset(x.right));
            case EQUALS :
                return equal(x.left, x.right);
            case NOT_EQUALS :
                return !equal(x.left, x.right);
            case IN :
                return isIn(x.left, x.right);
            case NOT_IN :
                return !isIn(x.left, x.right);
            case MINUS :
                // Special exception to allow "0-8" to not throw an exception,
                // where 7 is the maximum allowed integer (when bitwidth==4)
                // (likewise, when bitwidth==5, then +15 is the maximum allowed
                // integer, and we want to allow 0-16 without throwing an
                // exception)
                if (a instanceof ExprConstant && ((ExprConstant) a).op == ExprConstant.Op.NUMBER && ((ExprConstant) a).num() == 0)
                    if (b instanceof ExprConstant && ((ExprConstant) b).op == ExprConstant.Op.NUMBER && ((ExprConstant) b).num() == max + 1)
                        return min;
                // [AM]
                // if (x.left.type().is_int()) return
                // trunc(cint(x.left)-cint(x.right)); else return
                // cset(x.left).difference(cset(x.right));
                return cset(x.left).difference(cset(x.right));
            case IMINUS :
                return trunc(cint(x.left) - cint(x.right));
            case PLUS :
                return cset(x.left).union(cset(x.right));
            // [AM]
            // if (x.left.type().is_int()) return
            // trunc(cint(x.left)+cint(x.right)); else return
            // cset(x.left).union(cset(x.right));
            case IPLUS :
                return trunc(cint(x.left) + cint(x.right));
            case PLUSPLUS :
                return cset(x.left).override(cset(x.right));
            case MUL :
                return trunc(cint(x.left) * cint(x.right));
            case DIV : {
                int p = cint(x.left), q = cint(x.right), r = (p == 0 ? 0 : (q == 0 ? (p < 0 ? 1 : -1) : (p / q)));
                return trunc(r);
            }
            case REM : {
                int p = cint(x.left), q = cint(x.right), r = (p == 0 ? 0 : (q == 0 ? (p < 0 ? 1 : -1) : (p / q)));
                return trunc(p - r * q);
            }
        }
        throw new ErrorFatal(x.pos, "Unsupported operator (" + x.op + ") encountered during ExprBinary.accept()");
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprList x) throws Err {
        if (x.op == ExprList.Op.AND) {
            for (Expr e : x.args)
                if (!cform(e))
                    return false;
            return true;
        }
        if (x.op == ExprList.Op.OR) {
            for (Expr e : x.args)
                if (cform(e))
                    return true;
            return false;
        }
        if (x.op == ExprList.Op.TOTALORDER) {
            SimTupleset elem = cset(x.args.get(0)), first = cset(x.args.get(1)), next = cset(x.args.get(2));
            return next.totalOrder(elem, first);
        }
        SimTupleset[] ans = new SimTupleset[x.args.size()];
        for (int i = 1; i < ans.length; i++) {
            for (int j = 0; j < i; j++) {
                if (ans[i] == null)
                    if ((ans[i] = cset(x.args.get(i))).empty())
                        continue;
                if (ans[j] == null)
                    if ((ans[j] = cset(x.args.get(j))).empty())
                        continue;
                if (ans[j].intersects(ans[i]))
                    return false;
            }
        }
        return true;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprCall x) throws Err {
        final Func f = x.fun;
        final int n = f.count();
        final Object candidate = n == 0 ? cacheForConstants.get(f) : null;
        if (candidate != null)
            return candidate;
        final Expr body = f.getBody();
        if (body.type().arity() < 0 || body.type().arity() != f.returnDecl.type().arity())
            throw new ErrorType(body.span(), "Function return value not fully resolved.");
        for (Func ff : current_function)
            if (ff == f)
                throw new ErrorSyntax(x.span(), "" + f + " cannot call itself recursively!");
        Env<ExprVar,Object> newenv = new Env<ExprVar,Object>();
        List<SimTupleset> list = new ArrayList<SimTupleset>(x.args.size());
        for (int i = 0; i < n; i++) {
            SimTupleset ts = cset(x.args.get(i));
            newenv.put(f.get(i), ts);
            list.add(ts);
        }
        final SimCallback cb = callbacks.get(f);
        if (cb != null) {
            try {
                Object answer = cb.compute(f, list);
                if (answer != null) {
                    if (x.args.size() == 0)
                        cacheForConstants.put(f, answer);
                    return answer;
                }
            } catch (Exception ex) {
                // if the callback failed, we can just continue with our
                // original attempt to evaluate this call
            }
        }
        Env<ExprVar,Object> oldenv = env;
        env = newenv;
        current_function.add(f);
        Object ans = visitThis(body);
        env = oldenv;
        current_function.remove(current_function.size() - 1);
        if (f.count() == 0)
            cacheForConstants.put(f, ans);
        return ans;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprConstant x) throws Err {
        switch (x.op) {
            case NUMBER :
                int n = x.num();
                // [am] const
                // if (n<min) throw new ErrorType(x.pos, "Current bitwidth is
                // set to "+bitwidth+", thus this integer constant "+n+" is
                // smaller than the minimum integer "+min);
                // if (n>max) throw new ErrorType(x.pos, "Current bitwidth is
                // set to "+bitwidth+", thus this integer constant "+n+" is
                // bigger than the maximum integer "+max);
                return n;
            case FALSE :
                return Boolean.FALSE;
            case TRUE :
                return Boolean.TRUE;
            case MIN :
                return min;
            case MAX :
                return max;
            case EMPTYNESS :
                return SimTupleset.EMPTY;
            case STRING :
                return SimTupleset.make(x.string);
            case NEXT :
                return SimTupleset.makenext(min, max);
            case IDEN :
                return cset(Sig.UNIV).iden();
        }
        throw new ErrorFatal(x.pos, "Unsupported operator (" + x.op + ") encountered during ExprConstant.accept()");
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprITE x) throws Err {
        if (cform(x.cond))
            return visitThis(x.left);
        else
            return visitThis(x.right);
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprLet x) throws Err {
        env.put(x.var, visitThis(x.expr));
        Object ans = visitThis(x.sub);
        env.remove(x.var);
        return ans;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprUnary x) throws Err {
        switch (x.op) {
            case EXACTLYOF :
            case LONEOF :
            case ONEOF :
            case SETOF :
            case SOMEOF :
                return cset(x.sub);
            case NOOP :
                return visitThis(x.sub);
            case CARDINALITY :
                return trunc(cset(x.sub).size());
            case NO :
                return cset(x.sub).empty();
            case LONE :
                return cset(x.sub).longsize() <= 1;
            case ONE :
                return cset(x.sub).longsize() == 1;
            case SOME :
                return cset(x.sub).longsize() >= 1;
            case NOT :
                return cform(x.sub) ? Boolean.FALSE : Boolean.TRUE;
            case CAST2SIGINT :
                return SimTupleset.make(SimTuple.make(SimAtom.make(cint(x.sub))));
            case CAST2INT :
                return trunc(cset(x.sub).sum());
            case CLOSURE :
                return cset(x.sub).closure();
            case RCLOSURE :
                return cset(x.sub).closure().union(cset(ExprConstant.IDEN));
            case TRANSPOSE :
                return cset(x.sub).transpose();
        }
        throw new ErrorFatal(x.pos, "Unsupported operator (" + x.op + ") encountered during ExprUnary.accept()");
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprVar x) throws Err {
        Object ans = env.get(x);
        if (ans == null)
            ans = sfs.get(x);
        if (ans == null) {
            SimAtom a = SimAtom.make(x.label);
            if (!hasAtom(a))
                throw new ErrorFatal(x.pos, "Variable \"" + x + "\" is not bound to a legal value during translation.\n");
            ans = SimTupleset.make(SimTuple.make(a));
        }
        return ans;
    }

    /** {@inheritDoc} */
    @Override
    public SimTupleset visit(Sig x) throws Err {
        if (x.isSame(Sig.NONE))
            return SimTupleset.EMPTY;
        if (x.isSame(Sig.SEQIDX))
            return SimTupleset.make(0, maxseq - 1);
        if (x.isSame(Sig.SIGINT))
            return SimTupleset.make(min, max);
        if (x.isSame(Sig.STRING)) {
            if (cacheSTRING == null) {
                cacheSTRING = SimTupleset.EMPTY;
                for (Map.Entry<Expr,SimTupleset> e : sfs.entrySet())
                    if (e.getKey() instanceof Field || e.getKey() instanceof ExprVar) {
                        for (SimTuple t : e.getValue())
                            for (int i = t.arity() - 1; i >= 0; i--) {
                                String a = t.get(i).toString();
                                if (a.length() > 0 && a.charAt(0) == '"')
                                    cacheSTRING = cacheSTRING.union(SimTuple.make(t.get(i)));
                            }
                    }
            }
            return cacheSTRING;
        }
        if (x == Sig.UNIV) {
            if (cacheUNIV == null) {
                cacheUNIV = SimTupleset.make(min, max);
                for (Map.Entry<Expr,SimTupleset> e : sfs.entrySet())
                    if (e.getKey() instanceof PrimSig && ((PrimSig) (e.getKey())).isTopLevel())
                        cacheUNIV = cacheUNIV.union(e.getValue());
                cacheUNIV = cacheUNIV.union(visit(Sig.STRING));
            }
            return cacheUNIV;
        }
        Object ans = sfs.get(x);
        if (ans instanceof SimTupleset)
            return (SimTupleset) ans;
        else
            throw new ErrorFatal("Unknown sig " + x + " encountered during evaluation.");
    }

    /** {@inheritDoc} */
    @Override
    public SimTupleset visit(Field x) throws Err {
        if (x.defined) {
            final ExprVar v = (ExprVar) (x.sig.decl.get());
            final Expr b = x.decl().expr;
            final Env<ExprVar,Object> oldenv = env;
            env = new Env<ExprVar,Object>();
            if (!b.hasVar(v)) {
                SimTupleset ans = cset(x.sig).product(cset(b));
                env = oldenv;
                return ans;
            }
            SimTupleset ans = SimTupleset.EMPTY;
            for (SimTuple a : visit(x.sig)) {
                SimTupleset left = SimTupleset.make(a);
                env.put(v, left);
                SimTupleset right = cset(b);
                env.remove(v);
                ans = left.product(right).union(ans);
            }
            env = oldenv;
            return ans;
        }
        Object ans = sfs.get(x);
        if (ans instanceof SimTupleset)
            return (SimTupleset) ans;
        else
            throw new ErrorFatal("Unknown field " + x + " encountered during evaluation.");
    }

    /**
     * Helper method for enumerating all possibilties for a
     * quantification-expression.
     */
    private int enumerate(final TempList<SimTuple> store, int sum, final ExprQt x, final Expr body, final int i) throws Err { // if op is ALL NO SOME ONE LONE then it always returns
                                                                                                                             // 0 1 2
        final int n = x.count();
        final ExprVar v = x.get(i);
        final Expr bound = x.getBound(i);
        final SimTupleset e = cset(bound);
        final Iterator<SimTupleset> it;
        switch (bound.mult()) {
            case LONEOF :
                it = e.loneOf();
                break;
            case ONEOF :
                it = e.oneOf();
                break;
            case SOMEOF :
                it = e.someOf();
                break;
            default :
                it = e.setOf();
        }
        while (it.hasNext()) {
            final SimTupleset binding = it.next();
            if (bound.mult == 2 && !isIn(binding, bound))
                continue;
            env.put(v, binding);
            if (i < n - 1)
                sum = enumerate(store, sum, x, body, i + 1);
            else if (x.op == ExprQt.Op.SUM)
                sum += cint(body);
            else if (x.op != ExprQt.Op.COMPREHENSION)
                sum += cform(body) ? 1 : 0;
            else if (cform(body)) {
                SimTuple a = null, b;
                for (int j = 0; j < n; j++) {
                    b = ((SimTupleset) (env.get(x.get(j)))).getTuple();
                    if (a == null)
                        a = b;
                    else
                        a = a.product(b);
                }
                store.add(a);
            }
            env.remove(v);
            if (sum >= 2 && x.op != ExprQt.Op.COMPREHENSION && x.op != ExprQt.Op.SUM)
                return 2; // no need to enumerate further
        }
        return sum;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(ExprQt x) throws Err {
        Expr xx = x.desugar();
        if (xx instanceof ExprQt)
            x = (ExprQt) xx;
        else
            return visitThis(xx);
        if (x.op == ExprQt.Op.COMPREHENSION) {
            TempList<SimTuple> ans = new TempList<SimTuple>();
            enumerate(ans, 0, x, x.sub, 0);
            return SimTupleset.make(ans.makeConst());
        }
        if (x.op == ExprQt.Op.ALL)
            return enumerate(null, 0, x, x.sub.not(), 0) == 0;
        if (x.op == ExprQt.Op.NO)
            return enumerate(null, 0, x, x.sub, 0) == 0;
        if (x.op == ExprQt.Op.SOME)
            return enumerate(null, 0, x, x.sub, 0) >= 1;
        if (x.op == ExprQt.Op.LONE)
            return enumerate(null, 0, x, x.sub, 0) <= 1;
        if (x.op == ExprQt.Op.ONE)
            return enumerate(null, 0, x, x.sub, 0) == 1;
        if (x.op == ExprQt.Op.SUM)
            return trunc(enumerate(null, 0, x, x.sub, 0));
        throw new ErrorFatal(x.pos, "Unsupported operator (" + x.op + ") encountered during ExprQt.accept()");
    }

    /**
     * Helper method that evaluates the formula "a in b" where b.mult==0
     */
    public boolean isIn(SimTuple a, Expr b) throws Err {
        b = b.deNOP();
        if (b instanceof PrimSig && ((PrimSig) b).builtin) {
            if (a.arity() != 1)
                return false;
            if (b.isSame(Sig.UNIV))
                return true;
            if (b.isSame(Sig.NONE))
                return false;
            if (b.isSame(Sig.SEQIDX)) {
                Integer i = a.get(0).toInt(null);
                return i != null && i >= 0 && i < maxseq;
            }
            if (b.isSame(Sig.SIGINT)) {
                Integer i = a.get(0).toInt(null);
                return i != null;
            }
            if (b.isSame(Sig.STRING)) {
                String at = a.get(0).toString();
                return at.length() > 0 && (at.charAt(0) == '\"');
            }
        }
        if (b instanceof ExprBinary && ((ExprBinary) b).op == ExprBinary.Op.ARROW) {
            Expr left = ((ExprBinary) b).left, right = ((ExprBinary) b).right;
            int ll = left.type().arity(), rr = right.type().arity();
            if (ll <= rr)
                return isIn(a.head(ll), left) && isIn(a.tail(rr), right);
            return isIn(a.tail(rr), right) && isIn(a.head(ll), left);
        }
        if (b instanceof ExprBinary && ((ExprBinary) b).op == ExprBinary.Op.PLUS) {
            return isIn(a, ((ExprBinary) b).left) || isIn(a, ((ExprBinary) b).right);
        }
        if (b instanceof ExprBinary && ((ExprBinary) b).op == ExprBinary.Op.MINUS) {
            return isIn(a, ((ExprBinary) b).left) && !isIn(a, ((ExprBinary) b).right);
        }
        return cset(b).has(a);
    }

    /** Helper method that evaluates the formula "a = b" */
    public boolean equal(Expr a, Expr b) throws Err {
        if (a.type().is_bool)
            return cform(a) == cform(b);
        // [AM] if (a.type().is_int()) return cint(a)==cint(b);
        if (a.type().arity() <= 0 || a.type().arity() != b.type().arity())
            return false; // type mismatch
        if (a.isSame(b))
            return true;
        else
            return cset(a).equals(cset(b));
    }

    /** Helper method that evaluates the formula "a in b" */
    public boolean isIn(Expr a, Expr b) throws Err {
        if (a.type().arity() <= 0 || a.type().arity() != b.type().arity())
            return false; // type mismatch
        if (b.isSame(Sig.UNIV))
            return true; // everything is a subset of UNIV
        if (a.isSame(b))
            return true; // if a==b then a is a subset of b
        return isIn(cset(a), b);
    }

    /** Helper method that evaluates the formula "a in b" */
    private boolean isIn(SimTupleset a, Expr b) throws Err {
        b = b.deNOP();
        if (b instanceof ExprBinary && b.mult != 0 && ((ExprBinary) b).op.isArrow) {
            // Handles possible "binary" or higher-arity multiplicity
            return isInBinary(a, (ExprBinary) b);
        }
        if (b instanceof ExprUnary) {
            // Handles possible "unary" multiplicity
            ExprUnary y = (ExprUnary) b;
            if (y.op == ExprUnary.Op.EXACTLYOF) {
                b = y.sub.deNOP();
                return a.equals(cset(b));
            } else if (y.op == ExprUnary.Op.ONEOF) {
                b = y.sub.deNOP();
                if (!(a.longsize() == 1))
                    return false;
            } else if (y.op == ExprUnary.Op.LONEOF) {
                b = y.sub.deNOP();
                if (!(a.longsize() <= 1))
                    return false;
            } else if (y.op == ExprUnary.Op.SOMEOF) {
                b = y.sub.deNOP();
                if (!(a.longsize() >= 1))
                    return false;
            } else if (y.op != ExprUnary.Op.SETOF) {
                b = y.sub.deNOP();
            }
        }
        for (SimTuple t : a)
            if (!isIn(t, b))
                return false;
        return true;
    }

    /**
     * Helper method that evaluates the formula "r in (a ?->? b)"
     */
    private boolean isInBinary(SimTupleset R, ExprBinary ab) throws Err {
        // Special check for ISSEQ_ARROW_LONE
        if (ab.op == ExprBinary.Op.ISSEQ_ARROW_LONE) {
            List<SimAtom> list = R.getAllAtoms(0);
            int next = 0;
            SimAtom nextStr = SimAtom.make("0");
            while (list.size() > 0) {
                for (int n = list.size(), i = 0;; i++)
                    if (i >= n)
                        return false;
                    else if (nextStr == list.get(i)) {
                        list.set(i, list.get(n - 1));
                        list.remove(n - 1);
                        next++;
                        break;
                    }
                if (list.size() == 0)
                    break;
                if (next < 0 || next >= maxseq)
                    return false; // list.size()>0 and yet we've exhausted
                                 // 0..maxseq-1, so indeed there are illegal
                                 // atoms
                nextStr = SimAtom.make(next);
            }
        }
        // "R in A ->op B" means for each tuple a in A, there are "op" tuples in
        // r that begins with a.
        for (SimTuple left : cset(ab.left)) {
            SimTupleset ans = R.beginWith(left);
            switch (ab.op) {
                case ISSEQ_ARROW_LONE :
                case ANY_ARROW_LONE :
                case SOME_ARROW_LONE :
                case ONE_ARROW_LONE :
                case LONE_ARROW_LONE :
                    if (!(ans.longsize() <= 1))
                        return false;
                    else
                        break;
                case ANY_ARROW_ONE :
                case SOME_ARROW_ONE :
                case ONE_ARROW_ONE :
                case LONE_ARROW_ONE :
                    if (!(ans.longsize() == 1))
                        return false;
                    else
                        break;
                case ANY_ARROW_SOME :
                case SOME_ARROW_SOME :
                case ONE_ARROW_SOME :
                case LONE_ARROW_SOME :
                    if (!(ans.longsize() >= 1))
                        return false;
                    else
                        break;
            }
            if (!isIn(ans, ab.right))
                return false;
        }
        // "R in A op-> B" means for each tuple b in B, there are "op" tuples in
        // r that end with b.
        for (SimTuple right : cset(ab.right)) {
            SimTupleset ans = R.endWith(right);
            switch (ab.op) {
                case LONE_ARROW_ANY :
                case LONE_ARROW_SOME :
                case LONE_ARROW_ONE :
                case LONE_ARROW_LONE :
                    if (!(ans.longsize() <= 1))
                        return false;
                    else
                        break;
                case ONE_ARROW_ANY :
                case ONE_ARROW_SOME :
                case ONE_ARROW_ONE :
                case ONE_ARROW_LONE :
                    if (!(ans.longsize() == 1))
                        return false;
                    else
                        break;
                case SOME_ARROW_ANY :
                case SOME_ARROW_SOME :
                case SOME_ARROW_ONE :
                case SOME_ARROW_LONE :
                    if (!(ans.longsize() >= 1))
                        return false;
                    else
                        break;
            }
            if (!isIn(ans, ab.left))
                return false;
        }
        return true;
    }

    /**
     * Checks whether this instance satisfies every fact defined in the given model.
     *
     * @param world - this must be the root of the Alloy model
     * @return an empty String if yes, nonempty String if no
     */
    public String validate(Module world) {
        try {
            for (Sig s : world.getAllReachableSigs())
                if (!s.builtin) {
                    if (s.isLone != null && !(visit(s).longsize() <= 1))
                        return "There can be at most one " + s;
                    if (s.isOne != null && !(visit(s).longsize() == 1))
                        return "There must be exactly one " + s;
                    if (s.isSome != null && !(visit(s).longsize() >= 1))
                        return "There must be at least one " + s;
                    if (s instanceof SubsetSig) {
                        SubsetSig p = (SubsetSig) s;
                        Expr sum = null;
                        for (Sig par : p.parents)
                            sum = par.plus(sum);
                        if (p.exact) {
                            if (!equal(s, sum))
                                return "Sig " + s + " must be equal to the union of its parents " + p.parents;
                        } else {
                            if (!isIn(s, sum))
                                return "Sig " + s + " must be equal or subset of its parents " + p.parents;
                        }
                    } else if (s != Sig.UNIV && s != Sig.NONE) {
                        PrimSig p = (PrimSig) s;
                        if (!isIn(s, p.parent))
                            return "Sig " + s + " must be equal or subset of its parent " + p.parent;
                    }
                    if (s.isAbstract != null) {
                        Expr sum = null;
                        for (Sig x : ((PrimSig) s).children())
                            sum = x.plus(sum);
                        if (sum != null && !equal(s, sum))
                            return "Abstract sig " + s + " must be equal to the union of its subsigs";
                    }
                    for (Decl d : s.getFieldDecls())
                        for (ExprHasName f : d.names)
                            if (!((Field) f).defined) {
                                if (!cform(s.decl.get().join(f).in(d.expr).forAll(s.decl))) {
                                    return "Field " + f + " violated its bound: " + visit((Field) f) + "\n" + d.expr;
                                }
                                SimTupleset setS = visit(s);
                                SimTupleset setF = visit((Field) f);
                                for (SimAtom x : setF.getAllAtoms(0))
                                    if (!setS.has(x))
                                        return "Field " + f + " first column has extra atom: " + setF + " not in " + setS;
                            }
                    for (Decl d : s.getFieldDecls()) {
                        if (d.disjoint != null && d.names.size() > 0) {
                            if (!cform(ExprList.makeDISJOINT(null, null, d.names)))
                                return "Fields must be disjoint.";
                        }
                        if (d.disjoint2 != null)
                            for (ExprHasName f : d.names) {
                                Decl that = s.oneOf("that");
                                Expr formula = s.decl.get().equal(that.get()).not().implies(s.decl.get().join(f).intersect(that.get().join(f)).no());
                                if (!cform(formula.forAll(that).forAll(s.decl)))
                                    return "Fields must be disjoint.";
                            }
                    }
                    for (Expr f : s.getFacts()) {
                        if (!cform(f.forAll(s.decl))) {
                            f = f.deNOP();
                            if (f instanceof ExprUnary) {
                                ExprUnary u = (ExprUnary) f;
                                f = u.sub.deNOP();
                                if (f instanceof ExprBinary) {
                                    ExprBinary b = (ExprBinary) f;
                                    if (b.op == ExprBinary.Op.JOIN && b.left.isSame(s.decl.get()) && b.right.deNOP() instanceof Field) {
                                        String n = ((Field) (b.right.deNOP())).label;
                                        if (u.op == ExprUnary.Op.SOME)
                                            return "The " + n + " cannot be empty.";
                                        if (u.op == ExprUnary.Op.LONE)
                                            return "The " + n + " cannot have more than one value.";
                                        if (u.op == ExprUnary.Op.ONE)
                                            return "The " + n + " must have exactly one value.";
                                        if (u.op == ExprUnary.Op.NO)
                                            return "The " + n + " must be empty.";
                                    }
                                }
                            }
                            return "Cannot violate a consistency constraint";
                        }
                    }
                }
            for (Module m : world.getAllReachableModules())
                for (Pair<String,Expr> f : m.getAllFacts())
                    if (!cform(f.b)) {
                        String err = f.a;
                        if (err.matches("^fact\\$[0-9][0-9]*"))
                            err = f.b.toString();
                        if (err.length() >= 2 && err.startsWith("\"") && err.endsWith("\""))
                            err = err.substring(1, err.length() - 1);
                        return "Violation: " + err;
                    }
            return "";
        } catch (Err ex) {
            return "An internal error has occured:\n" + ex.dump();
        }
    }
}
