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

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorAPI;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4.Version;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Sig.PrimSig;
import edu.mit.csail.sdg.ast.Sig.SubsetSig;
import edu.mit.csail.sdg.ast.Type;

/**
 * This helper class contains helper routines for writing an A4Solution object
 * out as an XML file.
 */

public final class A4SolutionWriter {

    /** Maps each Sig, Field, and Skolem to a unique id. */
    private final IdentityHashMap<Expr,String> map       = new IdentityHashMap<Expr,String>();

    /** This is the solution we're writing out. */
    private final A4Solution                   sol;

    /**
     * This is the A4Reporter that we're sending diagnostic messages to; can be null
     * if none.
     */
    private final A4Reporter                   rep;

    /** This is the list of toplevel sigs. */
    private final List<PrimSig>                toplevels = new ArrayList<PrimSig>();

    /** This is the output file. */
    private final PrintWriter                  out;

    /**
     * Helper method that returns a unique id for the given Sig, Field, or Skolem.
     */
    private String map(Expr obj) {
        String id = map.get(obj);
        if (id == null) {
            id = Integer.toString(map.size());
            map.put(obj, id);
        }
        return id;
    }

    /**
     * Helper method that returns the list of direct subsignatures.
     */
    private Iterable<PrimSig> children(PrimSig x) throws Err {
        if (x == Sig.NONE)
            return new ArrayList<PrimSig>();
        if (x != Sig.UNIV)
            return x.children();
        else
            return toplevels;
    }

    /** Write the given Expr and its Type. */
    private boolean writeExpr(String prefix, Expr expr) throws Err {
        Type type = expr.type();
        if (!type.hasTuple())
            return false;
        if (sol != null) {
            // Check to see if the tupleset is *really* fully contained inside
            // "type".
            // If not, then grow "type" until the tupleset is fully contained
            // inside "type"
            Expr sum = type.toExpr();
            int lastSize = (-1);
            while (true) {
                A4TupleSet ts = (A4TupleSet) (sol.eval(expr.minus(sum)));
                int n = ts.size();
                if (n <= 0)
                    break;
                if (lastSize > 0 && lastSize <= n)
                    throw new ErrorFatal("An internal error occurred in the evaluator.");
                lastSize = n;
                Type extra = ts.iterator().next().type();
                type = type.merge(extra);
                sum = sum.plus(extra.toExpr());
            }
            // Now, write out the tupleset
            A4TupleSet ts = (A4TupleSet) (sol.eval(expr));
            for (A4Tuple t : ts) {
                if (prefix.length() > 0) {
                    out.print(prefix);
                    prefix = "";
                }
                out.print("   <tuple>");
                for (int i = 0; i < t.arity(); i++)
                    Util.encodeXMLs(out, " <atom label=\"", t.atom(i), "\"/>");
                out.print(" </tuple>\n");
            }
        }
        // Now, write out the type
        if (prefix.length() > 0)
            return false;
        for (List<PrimSig> ps : type.fold()) {
            out.print("   <types>");
            for (PrimSig sig : ps)
                Util.encodeXMLs(out, " <type ID=\"", map(sig), "\"/>");
            out.print(" </types>\n");
        }
        return true;
    }

    /** Write the given Sig. */
    private A4TupleSet writesig(final Sig x) throws Err {
        A4TupleSet ts = null, ts2 = null;
        if (x == Sig.NONE)
            return null; // should not happen, but we test for it anyway
        if (sol == null && x.isMeta != null)
            return null; // When writing the metamodel, skip the metamodel sigs!
        if (x instanceof PrimSig)
            for (final PrimSig sub : children((PrimSig) x)) {
                A4TupleSet ts3 = writesig(sub);
                if (ts2 == null)
                    ts2 = ts3;
                else
                    ts2 = ts2.plus(ts3);
            }
        if (rep != null)
            rep.write(x);
        Util.encodeXMLs(out, "\n<sig label=\"", x.label, "\" ID=\"", map(x));
        if (x instanceof PrimSig && x != Sig.UNIV)
            Util.encodeXMLs(out, "\" parentID=\"", map(((PrimSig) x).parent));
        if (x.builtin)
            out.print("\" builtin=\"yes");
        if (x.isAbstract != null)
            out.print("\" abstract=\"yes");
        if (x.isOne != null)
            out.print("\" one=\"yes");
        if (x.isLone != null)
            out.print("\" lone=\"yes");
        if (x.isSome != null)
            out.print("\" some=\"yes");
        if (x.isPrivate != null)
            out.print("\" private=\"yes");
        if (x.isMeta != null)
            out.print("\" meta=\"yes");
        if (x instanceof SubsetSig && ((SubsetSig) x).exact)
            out.print("\" exact=\"yes");
        if (x.isEnum != null)
            out.print("\" enum=\"yes");
        out.print("\">\n");
        try {
            if (sol != null && x != Sig.UNIV && x != Sig.SIGINT && x != Sig.SEQIDX) {
                ts = (sol.eval(x));
                for (A4Tuple t : ts.minus(ts2))
                    Util.encodeXMLs(out, "   <atom label=\"", t.atom(0), "\"/>\n");
            }
        } catch (Throwable ex) {
            throw new ErrorFatal("Error evaluating sig " + x.label, ex);
        }
        if (x instanceof SubsetSig)
            for (Sig p : ((SubsetSig) x).parents)
                Util.encodeXMLs(out, "   <type ID=\"", map(p), "\"/>\n");
        out.print("</sig>\n");
        for (Field field : x.getFields())
            writeField(field);
        return ts;
    }

    /** Write the given Field. */
    private void writeField(Field x) throws Err {
        try {
            if (sol == null && x.isMeta != null)
                return; // when writing the metamodel, skip the metamodel
                       // fields!
            if (x.type().hasNoTuple())
                return; // we do not allow "none" in the XML file's type
                       // declarations
            if (rep != null)
                rep.write(x);
            Util.encodeXMLs(out, "\n<field label=\"", x.label, "\" ID=\"", map(x), "\" parentID=\"", map(x.sig));
            if (x.isPrivate != null)
                out.print("\" private=\"yes");
            if (x.isMeta != null)
                out.print("\" meta=\"yes");
            out.print("\">\n");
            writeExpr("", x);
            out.print("</field>\n");
        } catch (Throwable ex) {
            throw new ErrorFatal("Error evaluating field " + x.sig.label + "." + x.label, ex);
        }
    }

    /** Write the given Skolem. */
    private void writeSkolem(ExprVar x) throws Err {
        try {
            if (sol == null)
                return; // when writing a metamodel, skip the skolems
            if (x.type().hasNoTuple())
                return; // we do not allow "none" in the XML file's type
                       // declarations
            StringBuilder sb = new StringBuilder();
            Util.encodeXMLs(sb, "\n<skolem label=\"", x.label, "\" ID=\"", map(x), "\">\n");
            if (writeExpr(sb.toString(), x)) {
                out.print("</skolem>\n");
            }
        } catch (Throwable ex) {
            throw new ErrorFatal("Error evaluating skolem " + x.label, ex);
        }
    }

    /**
     * If sol==null, write the list of Sigs as a Metamodel, else write the solution
     * as an XML file.
     */
    private A4SolutionWriter(A4Reporter rep, A4Solution sol, Iterable<Sig> sigs, int bitwidth, int maxseq, String originalCommand, String originalFileName, PrintWriter out, Iterable<Func> extraSkolems) throws Err {
        this.rep = rep;
        this.out = out;
        this.sol = sol;
        for (Sig s : sigs)
            if (s instanceof PrimSig && ((PrimSig) s).parent == Sig.UNIV)
                toplevels.add((PrimSig) s);
        out.print("<instance bitwidth=\"");
        out.print(bitwidth);
        out.print("\" maxseq=\"");
        out.print(maxseq);
        out.print("\" command=\"");
        Util.encodeXML(out, originalCommand);
        out.print("\" filename=\"");
        Util.encodeXML(out, originalFileName);
        if (sol == null)
            out.print("\" metamodel=\"yes");
        out.print("\">\n");
        writesig(Sig.UNIV);
        for (Sig s : sigs)
            if (s instanceof SubsetSig)
                writesig(s);
        if (sol != null)
            for (ExprVar s : sol.getAllSkolems()) {
                if (rep != null)
                    rep.write(s);
                writeSkolem(s);
            }
        int m = 0;
        if (sol != null && extraSkolems != null)
            for (Func f : extraSkolems)
                if (f.count() == 0 && f.call().type().hasTuple()) {
                    String label = f.label;
                    while (label.length() > 0 && label.charAt(0) == '$')
                        label = label.substring(1);
                    label = "$" + label;
                    try {
                        if (rep != null)
                            rep.write(f.call());
                        StringBuilder sb = new StringBuilder();
                        Util.encodeXMLs(sb, "\n<skolem label=\"", label, "\" ID=\"m" + m + "\">\n");
                        if (writeExpr(sb.toString(), f.call())) {
                            out.print("</skolem>\n");
                        }
                        m++;
                    } catch (Throwable ex) {
                        throw new ErrorFatal("Error evaluating skolem " + label, ex);
                    }
                }
        out.print("\n</instance>\n");
    }

    /**
     * If this solution is a satisfiable solution, this method will write it out in
     * XML format.
     */
    static void writeInstance(A4Reporter rep, A4Solution sol, PrintWriter out, Iterable<Func> extraSkolems, Map<String,String> sources) throws Err {
        if (!sol.satisfiable())
            throw new ErrorAPI("This solution is unsatisfiable.");
        try {
            Util.encodeXMLs(out, "<alloy builddate=\"", Version.buildDate(), "\">\n\n");
            new A4SolutionWriter(rep, sol, sol.getAllReachableSigs(), sol.getBitwidth(), sol.getMaxSeq(), sol.getOriginalCommand(), sol.getOriginalFilename(), out, extraSkolems);
            if (sources != null)
                for (Map.Entry<String,String> e : sources.entrySet()) {
                    Util.encodeXMLs(out, "\n<source filename=\"", e.getKey(), "\" content=\"", e.getValue(), "\"/>\n");
                }
            out.print("\n</alloy>\n");
        } catch (Throwable ex) {
            if (ex instanceof Err)
                throw (Err) ex;
            else
                throw new ErrorFatal("Error writing the solution XML file.", ex);
        }
        if (out.checkError())
            throw new ErrorFatal("Error writing the solution XML file.");
    }

    /**
     * Write the metamodel as &lt;instance&gt;..&lt;/instance&gt; in XML format.
     */
    public static void writeMetamodel(ConstList<Sig> sigs, String originalFilename, PrintWriter out) throws Err {
        try {
            new A4SolutionWriter(null, null, sigs, 4, 4, "show metamodel", originalFilename, out, null);
        } catch (Throwable ex) {
            if (ex instanceof Err)
                throw (Err) ex;
            else
                throw new ErrorFatal("Error writing the solution XML file.", ex);
        }
        if (out.checkError())
            throw new ErrorFatal("Error writing the solution XML file.");
    }
}
