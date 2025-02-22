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

import java.io.File;
import java.io.IOException;
import java.io.Reader;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4.XMLNode;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Sig.PrimSig;
import edu.mit.csail.sdg.ast.Sig.SubsetSig;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.A4SolutionReader;
import edu.mit.csail.sdg.translator.A4Tuple;
import edu.mit.csail.sdg.translator.A4TupleSet;

/**
 * This utility class parses an XML file into an AlloyInstance object.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 *
 * @modified [electrum] creates an AlloyInstance for a particular state after
 *           parsing the XML of a full instance trace (expressions evaluated in
 *           that state); whether elements are mutable is also registered
 */

public final class StaticInstanceReader {

    /** The resulting AlloyInstance object. */
    private final AlloyInstance                      ans;

    /** This is the list of toplevel sigs. */
    private final List<PrimSig>                      toplevels   = new ArrayList<PrimSig>();

    /**
     * This maps each Sig to its corresponding Visualizer AlloyType.
     */
    private final LinkedHashMap<Sig,AlloyType>       sig2type    = new LinkedHashMap<Sig,AlloyType>();

    /**
     * This maps each Sig to its corresponding unique Visualizer AlloyAtom (if
     * isMeta is true).
     */
    private final LinkedHashMap<Sig,AlloyAtom>       sig2atom    = new LinkedHashMap<Sig,AlloyAtom>();

    /**
     * This stores the "extends" relationship among sigs (if isMeta is true).
     */
    private final LinkedHashSet<AlloyTuple>          exts        = new LinkedHashSet<AlloyTuple>();
    private final LinkedHashSet<AlloyTuple>          mems        = new LinkedHashSet<AlloyTuple>();

    private final LinkedHashSet<AlloyAtom>          absts        = new LinkedHashSet<AlloyAtom>();
    private final LinkedHashSet<AlloyAtom>          ones        = new LinkedHashSet<AlloyAtom>();
    private final LinkedHashSet<AlloyAtom>          lones        = new LinkedHashSet<AlloyAtom>();
    private final LinkedHashSet<AlloyAtom>          somes        = new LinkedHashSet<AlloyAtom>();
    private final LinkedHashSet<AlloyAtom>          vars        = new LinkedHashSet<AlloyAtom>();
    private final LinkedHashSet<AlloyAtom>          enums        = new LinkedHashSet<AlloyAtom>();
    private final LinkedHashSet<AlloyAtom>          enummems        = new LinkedHashSet<AlloyAtom>();

    /**
     * This stores the "in" relationship among sigs (if isMeta is true).
     */
    private final LinkedHashSet<AlloyTuple>          ins         = new LinkedHashSet<AlloyTuple>();

    private final LinkedHashSet<AlloyTuple>          eqs         = new LinkedHashSet<AlloyTuple>();

    /**
     * This stores the set of Visualizer AlloySet objects we created.
     */
    private final Set<AlloySet>                      sets        = new LinkedHashSet<AlloySet>();

    /**
     * This maps each Visualizer AlloyRelation to its set of (possibly 0) tuples.
     */
    private final Map<AlloyRelation,Set<AlloyTuple>> rels        = new LinkedHashMap<AlloyRelation,Set<AlloyTuple>>();

    /**
     * This registers all elements that are not empty along the complete trace.
     */
    private final Set<AlloyElement> nonempty_elems = new LinkedHashSet<AlloyElement>();

    /**
     * For each sig A and B, if A extends B, and B is not univ, then (A,B) will be
     * in this map.
     */
    private final Map<AlloyType,AlloyType>           ts          = new LinkedHashMap<AlloyType,AlloyType>();

    /**
     * This maps each Visualizer AlloyAtom to its set of (possibly 0) AlloySet that
     * contains it.
     */
    private final Map<AlloyAtom,Set<AlloySet>>       atom2sets   = new LinkedHashMap<AlloyAtom,Set<AlloySet>>();

    /**
     * This maps each AlloyAtom label to the AlloyAtom we created for it.
     */
    private final Map<String,AlloyAtom>              string2atom = new LinkedHashMap<String,AlloyAtom>();

    /**
     * Create a new AlloyType whose label is unambiguous with any existing one.
     */
    private AlloyType makeType(String label, boolean isOne, boolean isAbstract, boolean isBuiltin, boolean isPrivate, boolean isMeta, boolean isEnum, boolean isVar) {
        label = Util.tailThis(label);
        while (true) {
            AlloyType ans = new AlloyType(label, isOne, isAbstract, isBuiltin, isPrivate, isMeta, isEnum, isVar);
            if (!sig2type.values().contains(ans))
                return ans;
            label = label + "'";
        }
    }

    /**
     * Create a new AlloySet whose label is unambiguous with any existing one.
     */
    private AlloySet makeSet(String label, boolean isPrivate, boolean isMeta, boolean isVar, boolean isSkolem, AlloyType type) {
        label = Util.tail(label);
        while (label.equals(Sig.UNIV.label) || label.equals(Sig.SIGINT.label) || label.equals(Sig.SEQIDX.label) || label.equals(Sig.STRING.label))
            label = label + "'";
        while (true) {
            AlloySet ans = new AlloySet(label, isPrivate, isMeta, isVar, isSkolem, type);
            if (!sets.contains(ans))
                return ans;
            label = label + "'";
        }
    }

    /**
     * Create a new AlloyRelation whose label is unambiguous with any existing one.
     */
    private AlloyRelation makeRel(String label, boolean isPrivate, boolean isMeta, boolean isVar, boolean isSkolem, List<AlloyType> types) {
        label = Util.tail(label);
        while (label.equals(Sig.UNIV.label) || label.equals(Sig.SIGINT.label) || label.equals(Sig.SEQIDX.label) || label.equals(Sig.STRING.label))
            label = label + "'";
        while (true) {
            AlloyRelation ans = new AlloyRelation(label, isPrivate, isMeta, isVar, isSkolem, types);
            if (!rels.containsKey(ans))
                return ans;
            label = label + "'";
        }
    }

    /**
     * Returns the AlloyType corresponding to the given sig; create an AlloyType for
     * it if none existed before.
     */
    private AlloyType sig(PrimSig s) throws Err {
        if (s == Sig.NONE)
            throw new ErrorFatal("Unexpected sig \"none\" encountered.");
        AlloyType ans = sig2type.get(s);
        if (ans == null) {
            ans = makeType(s.label, s.isOne != null, s.isAbstract != null, false, s.isPrivate != null, s.isMeta != null, s.isEnum != null, s.isVariable != null);
            sig2type.put(s, ans);
            if (s.parent != Sig.UNIV)
                ts.put(ans, sig(s.parent));
        }
        return ans;
    }

    /**
     * Returns the AlloyType corresponding to the given sig; create an AlloyType for
     * it if none existed before.
     */
    private AlloyType sigMETA(PrimSig s) throws Err {
        if (s == Sig.NONE)
            throw new ErrorFatal("Unexpected sig \"none\" encountered.");
        AlloyType type = sig2type.get(s);
        if (type != null)
            return type;
        if (s == Sig.UNIV)
            type = AlloyType.UNIV;
        else if (s == Sig.SIGINT)
            type = AlloyType.INT;
        else if (s == Sig.SEQIDX)
            type = AlloyType.SEQINT;
        else if (s == Sig.STRING)
            type = AlloyType.STRING;
        else
            type = makeType(s.label, s.isOne != null, s.isAbstract != null, false, s.isPrivate != null, s.isMeta != null, s.isEnum != null, s.isVariable != null);
        sig2type.put(s, type);
        AlloyAtom atom = new AlloyAtom(type, (type == AlloyType.SEQINT ? Integer.MIN_VALUE : Integer.MAX_VALUE), s.label);
        atom2sets.put(atom, new LinkedHashSet<AlloySet>());
        sig2atom.put(s, atom);
        if (s.parent != Sig.UNIV && s.parent != null)
            ts.put(type, sigMETA(s.parent));
        if (s.parent != null) {
            if (!s.isEnumMember())
                exts.add(new AlloyTuple(atom, sig2atom.get(s.parent)));
            else
                mems.add(new AlloyTuple(atom, sig2atom.get(s.parent)));
        }
        if (s.isEnum != null) {
            enums.add(atom);
            atom2sets.get(atom).add(AlloySet.ENUM);
        }else if (s.isAbstract != null) {
            absts.add(atom);
            atom2sets.get(atom).add(AlloySet.ABSTRACT);
        }
        if (s.isEnumMember()) {
            enummems.add(atom);
            atom2sets.get(atom).add(AlloySet.ENUMMEM);
        } else if (s.isOne != null) {
            ones.add(atom);
            atom2sets.get(atom).add(AlloySet.ONE);
        }
        if (s.isLone != null) {
            lones.add(atom);
            atom2sets.get(atom).add(AlloySet.LONE);
        }
        if (s.isSome != null) {
            somes.add(atom);
            atom2sets.get(atom).add(AlloySet.SOME);
        }
        if (s.isVariable != null) {
            vars.add(atom);
            atom2sets.get(atom).add(AlloySet.VAR);
        }

        Iterable<PrimSig> children = (s == Sig.UNIV ? toplevels : s.children());
        for (PrimSig sub : children)
            sigMETA(sub);
        return type;
    }

    /**
     * Returns the AlloyType corresponding to the given sig; create an AlloyType for
     * it if none existed before.
     */
    private void sigMETA(SubsetSig s) throws Err {
        AlloyAtom atom;
        AlloyType type = sig2type.get(s);
        if (type != null)
            return;
        type = makeType(s.label, s.isOne != null, s.isAbstract != null, false, s.isPrivate != null, s.isMeta != null, s.isEnum != null, s.isVariable != null);
        atom = new AlloyAtom(type, Integer.MAX_VALUE, s.label);
        atom2sets.put(atom, new LinkedHashSet<AlloySet>());
        sig2atom.put(s, atom);
        sig2type.put(s, type);
        ts.put(type, AlloyType.SET);
        for (Sig p : s.parents) {
            if (p instanceof SubsetSig)
                sigMETA((SubsetSig) p);
            else
                sigMETA((PrimSig) p);
            if (!s.exact)
                ins.add(new AlloyTuple(atom, sig2atom.get(p)));
            else
                eqs.add(new AlloyTuple(atom, sig2atom.get(p)));
        }
        if (s.isOne != null) {
            ones.add(atom);
            atom2sets.get(atom).add(AlloySet.ONE);
        }
        if (s.isLone != null) {
            lones.add(atom);
            atom2sets.get(atom).add(AlloySet.LONE);
        }
        if (s.isSome != null) {
            somes.add(atom);
            atom2sets.get(atom).add(AlloySet.SOME);
        }
        if (s.isVariable != null) {
            vars.add(atom);
            atom2sets.get(atom).add(AlloySet.VAR);
        }
    }

    /** Constructs the atoms corresponding to the given sig. */
    private void atoms(A4Solution sol, PrimSig s, int state) throws Err {
        Expr sum = Sig.NONE;
        for (PrimSig c : s.children()) {
            sum = sum.plus(c);
            atoms(sol, c, state);
        }
        A4TupleSet ts = (A4TupleSet) (sol.eval(s.minus(sum), state));
                                                              // This ensures
                                                              // that atoms
                                                              // will be
                                                              // associated
                                                              // with the most
                                                              // specific sig

        for (A4Tuple z : ts) {
            String atom = z.atom(0);
            int i, dollar = atom.lastIndexOf('$');
            try {
                i = Integer.parseInt(dollar >= 0 ? atom.substring(dollar + 1) : atom);
            } catch (NumberFormatException ex) {
                i = Integer.MAX_VALUE;
            }
            // [electrum] do not hide ids for variable singletons, their id may change between states
            AlloyAtom at = new AlloyAtom(sig(s), ts.size() == 1 && s.isVariable == null ? Integer.MAX_VALUE : i, atom);
            atom2sets.put(at, new LinkedHashSet<AlloySet>());
            string2atom.put(atom, at);
        }

        for (int i = 0; i < sol.getTraceLength(); i++)
            if (((A4TupleSet) (sol.eval(s.minus(sum), i))).size() > 0) {
                nonempty_elems.add(sig(s));
                break;
            }
    }

    /**
     * Construct an AlloySet or AlloyRelation corresponding to the given expression.
     */
    private void setOrRel(A4Solution sol, String label, Expr expr, boolean isPrivate, boolean isMeta, boolean isVar, boolean isSkolem, int state) throws Err {
        for (List<PrimSig> ps : expr.type().fold()) {
            if (ps.size() == 1) {
                PrimSig t = ps.get(0);
                AlloySet set = makeSet(label, isPrivate, isMeta, isVar, isSkolem, sig(t));
                sets.add(set);
                for (A4Tuple tp : (A4TupleSet) (sol.eval(expr.intersect(t), state))) {
                    atom2sets.get(string2atom.get(tp.atom(0))).add(set);
                }
                for (int i = 0; i < sol.getTraceLength(); i++)
                    if (((A4TupleSet) (sol.eval(expr.intersect(t), i))).size() > 0) {
                        nonempty_elems.add(set);
                        break;
                    }
            } else {
                Expr mask = null;
                List<AlloyType> types = new ArrayList<AlloyType>(ps.size());
                for (int i = 0; i < ps.size(); i++) {
                    types.add(sig(ps.get(i)));
                    if (mask == null)
                        mask = ps.get(i);
                    else
                        mask = mask.product(ps.get(i));
                }
                AlloyRelation rel = makeRel(label, isPrivate, isMeta, isVar, isSkolem, types);
                Set<AlloyTuple> ts = new LinkedHashSet<AlloyTuple>();
                for (A4Tuple tp : (A4TupleSet) (sol.eval(expr.intersect(mask), state))) {
                    AlloyAtom[] atoms = new AlloyAtom[tp.arity()];
                    for (int i = 0; i < tp.arity(); i++) {
                        atoms[i] = string2atom.get(tp.atom(i));
                        if (atoms[i] == null)
                            throw new ErrorFatal("Unexpected XML inconsistency: cannot resolve atom " + tp.atom(i));
                    }
                    ts.add(new AlloyTuple(atoms));
                }
                rels.put(rel, ts);
                for (int i = 0; i < sol.getTraceLength(); i++)
                    if (((A4TupleSet) (sol.eval(expr.intersect(mask), i))).size() > 0) {
                        nonempty_elems.add(rel);
                        break;
                    }

            }
        }
    }

    /** Parse the file into an AlloyInstance if possible. */
    private StaticInstanceReader(XMLNode root, int state) throws Err {
        XMLNode inst = null;
        for (XMLNode sub : root)
            if (sub.is("instance")) {
                inst = sub;
                break;
            }
        if (inst == null)
            throw new ErrorSyntax("The XML file must contain an <instance> element.");
        boolean isMeta = "yes".equals(inst.getAttribute("metamodel"));
        A4Solution sol = A4SolutionReader.read(new ArrayList<Sig>(), root);
        for (Sig s : sol.getAllReachableSigs())
            if (s instanceof PrimSig && ((PrimSig) s).parent == Sig.UNIV)
                toplevels.add((PrimSig) s);
        if (!isMeta) {
            sig2type.put(Sig.UNIV, AlloyType.UNIV);
            sig2type.put(Sig.SIGINT, AlloyType.INT);
            sig2type.put(Sig.SEQIDX, AlloyType.SEQINT);
            sig2type.put(Sig.STRING, AlloyType.STRING);
            ts.put(AlloyType.SEQINT, AlloyType.INT);
            for (int i = sol.min(), max = sol.max(), maxseq = sol.getMaxSeq(); i <= max; i++) {
                AlloyAtom at = new AlloyAtom(i >= 0 && i < maxseq ? AlloyType.SEQINT : AlloyType.INT, i, "" + i);
                atom2sets.put(at, new LinkedHashSet<AlloySet>());
                string2atom.put("" + i, at);
            }
            for (Sig s : sol.getAllReachableSigs())
                if (!s.builtin && s instanceof PrimSig)
                    sig((PrimSig) s);
            for (Sig s : toplevels)
                if (!s.builtin || s == Sig.STRING)
                    atoms(sol, (PrimSig) s, state);
            for (Sig s : sol.getAllReachableSigs())
                if (s instanceof SubsetSig)
                    setOrRel(sol, s.label, s, s.isPrivate != null, s.isMeta != null, s.isVariable != null, false, state);
            for (Sig s : sol.getAllReachableSigs())
                for (Field f : s.getFields())
                    setOrRel(sol, f.label, f, f.isPrivate != null, f.isMeta != null, f.isVariable != null, false, state);
            for (ExprVar s : sol.getAllSkolems())
                setOrRel(sol, s.label, s, false, false, false, true, state);
        }
        if (isMeta) {
            sigMETA(Sig.UNIV);
            for (Sig s : sol.getAllReachableSigs())
                if (s instanceof SubsetSig)
                    sigMETA((SubsetSig) s);
            for (Sig s : sol.getAllReachableSigs())
                for (Field f : s.getFields()) {
                    for (List<PrimSig> ps : f.type().fold()) {
                        List<AlloyType> types = new ArrayList<AlloyType>(ps.size());
                        AlloyAtom[] tuple = new AlloyAtom[ps.size()];
                        for (int i = 0; i < ps.size(); i++) {
                            types.add(sig(ps.get(i)));
                            tuple[i] = sig2atom.get(ps.get(i));
                        }
                        AlloyRelation rel = makeRel(f.label, f.isPrivate != null, false, f.isVariable != null, false, types);
                        rels.put(rel, Util.asSet(new AlloyTuple(tuple)));
                    }
                }
            if (ins.size() > 0) {
                sig2type.put(null, AlloyType.SET);
                rels.put(AlloyRelation.IN, ins);
            }
            if (eqs.size() > 0) {
                sig2type.put(null, AlloyType.SET);
                rels.put(AlloyRelation.EQ, eqs);
            }

            if (absts.size() > 0)
                sets.add(AlloySet.ABSTRACT);
            if (ones.size() > 0)
                sets.add(AlloySet.ONE);
            if (lones.size() > 0)
                sets.add(AlloySet.LONE);
            if (somes.size() > 0)
                sets.add(AlloySet.SOME);
            if (vars.size() > 0)
                sets.add(AlloySet.VAR);
            if (enums.size() > 0)
                sets.add(AlloySet.ENUM);
            if (enummems.size() > 0)
                sets.add(AlloySet.ENUMMEM);

            AlloyAtom univAtom = sig2atom.get(Sig.UNIV);
            AlloyAtom intAtom = sig2atom.get(Sig.SIGINT);
            AlloyAtom seqAtom = sig2atom.get(Sig.SEQIDX);
            AlloyAtom strAtom = sig2atom.get(Sig.STRING);
            for (Set<AlloyTuple> t : rels.values())
                for (AlloyTuple at : t)
                    if (at.getAtoms().contains(univAtom)) {
                        univAtom = null;
                        break;
                    }
            for (Set<AlloyTuple> t : rels.values())
                for (AlloyTuple at : t)
                    if (at.getAtoms().contains(intAtom)) {
                        intAtom = null;
                        break;
                    }
            for (Set<AlloyTuple> t : rels.values())
                for (AlloyTuple at : t)
                    if (at.getAtoms().contains(seqAtom)) {
                        seqAtom = null;
                        break;
                    }
            for (Set<AlloyTuple> t : rels.values())
                for (AlloyTuple at : t)
                    if (at.getAtoms().contains(strAtom)) {
                        strAtom = null;
                        break;
                    }
            if (univAtom != null) {
                for (Iterator<AlloyTuple> it = exts.iterator(); it.hasNext();) {
                    AlloyTuple at = it.next();
                    if (at.getStart() == univAtom || at.getEnd() == univAtom)
                        it.remove();
                }
                atom2sets.remove(univAtom);
            }
            if (strAtom != null) {
                for (Iterator<AlloyTuple> it = exts.iterator(); it.hasNext();) {
                    AlloyTuple at = it.next();
                    if (at.getStart() == strAtom || at.getEnd() == strAtom)
                        it.remove();
                }
                atom2sets.remove(strAtom);
            }
            if (intAtom != null && seqAtom != null) {
                for (Iterator<AlloyTuple> it = exts.iterator(); it.hasNext();) {
                    AlloyTuple at = it.next();
                    if (at.getStart() == intAtom || at.getEnd() == intAtom || at.getStart() == seqAtom || at.getEnd() == seqAtom)
                        it.remove();
                }
                atom2sets.remove(intAtom);
                atom2sets.remove(seqAtom);
            }
            if (exts.size() > 0) {
                rels.put(AlloyRelation.EXTENDS, exts);
            }
            if (mems.size() > 0) {
                rels.put(AlloyRelation.MEMBER, mems);
            }
        }
        AlloyModel am = new AlloyModel(sig2type.values(), sets, rels.keySet(), nonempty_elems, ts);
        int tracelen = Integer.valueOf(inst.getAttribute("tracelength"));
        int looplen = Integer.valueOf(inst.getAttribute("looplength"));
        ans = new AlloyInstance(sol, sol.getOriginalFilename(), sol.getOriginalCommand(), am, atom2sets, rels, isMeta,tracelen,looplen);
    }

    /** Parse the file into an AlloyInstance if possible. */
    public static AlloyInstance parseInstance(File file, int state) throws Err {
        try {
            return (new StaticInstanceReader(new XMLNode(file), state)).ans;
        } catch (IOException ex) {
            throw new ErrorFatal("Error reading the XML file: " + ex, ex);
        }
    }

    /**
     * Parse the file into an AlloyInstance if possible, then close the Reader
     * afterwards.
     */
    public static AlloyInstance parseInstance(Reader reader, int state) throws Err {
        try {
            return (new StaticInstanceReader(new XMLNode(reader), state)).ans;
        } catch (IOException ex) {
            throw new ErrorFatal("Error reading the XML file: " + ex, ex);
        }
    }
}
