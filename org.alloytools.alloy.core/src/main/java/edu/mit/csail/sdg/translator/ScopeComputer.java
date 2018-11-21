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

import static edu.mit.csail.sdg.ast.Sig.NONE;
import static edu.mit.csail.sdg.ast.Sig.SEQIDX;
import static edu.mit.csail.sdg.ast.Sig.SIGINT;
import static edu.mit.csail.sdg.ast.Sig.STRING;
import static edu.mit.csail.sdg.ast.Sig.UNIV;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentSkipListSet;
 
import kodkod.ast.ConstantExpression;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorAPI;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.alloy4.UniqueNameGenerator;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.CommandScope;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.PrimSig;

/**
 * Immutable; this class computes the scopes for each sig and computes the
 * bitwidth and maximum sequence length.
 * <p>
 * The scopes are determined as follows:
 * <p>
 * "run x": every topsig is scoped to <= 3 elements.
 * <p>
 * "run x for N": every topsig is scoped to <= N elements.
 * <p>
 * "run x for N but N1 SIG1, N2 SIG2...": <br>
 * Every sig following "but" is constrained explicitly. <br>
 * Any topsig that is <br>
 * a) not listed, and <br>
 * b) its scope is not derived otherwise <br>
 * will be scoped to have <= N elements.
 * <p>
 * "run x for N1 SIG1, N2 SIG2..." <br>
 * Every sig following "but" is constrained explicitly. <br>
 * Any topsig that is <br>
 * a) not listed, and <br>
 * b) its scope is not derived otherwise <br>
 * we will give an error message.
 * <p>
 * Please see ScopeComputer.java for the exact rules for deriving the missing
 * scopes.
 */
final class ScopeComputer {

    // It calls A4Solution's constructor

    /**
     * Stores the reporter that will receive diagnostic messages.
     */
    private final A4Reporter                       rep;

    /**
     * Stores the command that we're computing the scope for.
     */
    private final Command                          cmd;

    /**
     * The integer bitwidth of this solution's model; always between 1 and 30.
     */
    private int                                    bitwidth  = 4;

    /**
     * The maximum sequence length; always between 0 and (2^(bitwidth-1))-1.
     */
    private int                                    maxseq    = 4;

    /**
     * The number of STRING atoms to allocate; -1 if it was not specified.
     */
    private int                                    maxstring = (-1);

    /** The partial lower bound scope for each sig. */
    private final IdentityHashMap<String,List<String>> sig2PscopeL = new IdentityHashMap<String,List<String>>();
 
    /** The partial lower bound scope for each sig. */
    private final IdentityHashMap<String,List<String>> sig2PscopeU = new IdentityHashMap<String,List<String>>();    
 
    /** The partial lower-bound scope for each field. */
    private final IdentityHashMap<String,List<List<String>>> field2PscopeL = new IdentityHashMap<String,List<List<String>>>();
 
    /** The partial upper-bound scope for each field. */
    private final IdentityHashMap<String,List<List<String>>> field2PscopeU = new IdentityHashMap<String,List<List<String>>>();


    /** The scope for each sig. */
    private final IdentityHashMap<PrimSig,Integer> sig2scope = new IdentityHashMap<PrimSig,Integer>();

    /**
     * The sig's scope is exact iff it is in exact.keySet() (the value is
     * irrelevant).
     */
    private final IdentityHashMap<Sig,Sig>         exact     = new IdentityHashMap<Sig,Sig>();

    // To support Lower bound and include keyword
    /** The sig's scope has lower iff it is in exact.keySet() (the value is irrelevant). */
    private final IdentityHashMap<Sig,Sig> lower = new IdentityHashMap<Sig,Sig>();
 
    // To support Lower bound and include keyword
    /** The sig's scope has upper iff it is in exact.keySet() (the value is irrelevant). */
    private final IdentityHashMap<Sig,Sig> upper = new IdentityHashMap<Sig,Sig>();    

    /** The list of atoms. */
    private final List<String>                     atoms     = new ArrayList<String>();

    // store the extra integer values
    private final ConcurrentSkipListSet<Integer> exInt = new ConcurrentSkipListSet<Integer>();

    /**
     * This UniqueNameGenerator allows each sig's atoms to be distinct strings.
     */
    private final UniqueNameGenerator              un        = new UniqueNameGenerator();

    /** Returns the scope for a sig (or -1 if we don't know). */
    public int sig2scope(Sig sig) {
        if (sig == SIGINT)
            return 1 << bitwidth;
        if (sig == SEQIDX)
            return maxseq;
        if (sig == STRING)
            return maxstring;
        Integer y = sig2scope.get(sig);
        return (y == null) ? (-1) : y;
    }

    //Storing the lower bound of each sig determined in the inst block. In case of exact bound, the atoms are stored in both sig2PScopeL and sig2PScopeU.
    //So, whatever is in sig2PScopeL also exists in sig2PScopeU.
    //Lower-bound
    /** Returns the scope for a sig (or -1 if we don't know). */
    public int sig2PScopeL(Sig sig) {
        if (sig==SIGINT) return 1<<bitwidth;
        if (sig==SEQIDX) return maxseq;
        if (sig==STRING) return maxstring;
        List y = sig2PscopeL.get(sig.label);
        return (y==null) ? (-1) : y.size();
    }
 
    /** Returns the scope for a sig (or null if we don't know). */
    public List<String> sig2PscopeL(Sig sig) {
        return sig2PscopeL.get(sig.label);
    }    
 
    /** Returns the scope for a sig (or null if we don't know). */
    public List<String> sig2PscopeL(String label) {
        for(String l: sig2PscopeL.keySet()){
            if(l.equals(label))
                return sig2PscopeL.get(l);
        }
        return null;
    } 
 
    //Upper bound
    /** Returns the scope for a sig (or -1 if we don't know). */
    public int sig2PScopeU(Sig sig) {
        if (sig==SIGINT) return 1<<bitwidth;
        if (sig==SEQIDX) return maxseq;
        if (sig==STRING) return maxstring;
        List y = sig2PscopeU.get(sig.label);
        return (y==null) ? (-1) : y.size();
    }
 
    /** Returns the scope for a sig (or null if we don't know). */
    public List<String> sig2PscopeU(Sig sig) {
        return sig2PscopeU.get(sig.label);
    }    
 
    /** Returns the scope for a sig (or null if we don't know). */
    public List<String> sig2PscopeU(String label) {
        for(String l: sig2PscopeU.keySet()){
            if(l.equals(label))
                return sig2PscopeU.get(l);
        }
        return null;
    }
 
    /** Returns the scope for a sig (or -1 if we don't know). */
    public List<List<String>> field2PscopeL(Sig sig) {
        return field2PscopeL.get(sig.label);
    }    
 
    /** Returns the scope for a sig (or -1 if we don't know). */
    public List<List<String>> field2PscopeL(String label) {
        for(String l: field2PscopeL.keySet()){
            if(l.equals(label))
                return field2PscopeL.get(l);
        }
        return null;
    } 
    
    
    /** Returns the scope for a sig (or -1 if we don't know). */
    public List<List<String>> field2PscopeU(Sig sig) {
        return field2PscopeU.get(sig.label);
    }    
 
    /** Returns the scope for a sig (or -1 if we don't know). */
    public List<List<String>> field2PscopeU(String label) {
        for(String l: field2PscopeU.keySet()){
            if(l.equals(label))
                return field2PscopeU.get(l);
        }
        return null;
    } 

    /**
     * Sets the scope for a sig; returns true iff the sig's scope is changed by this
     * call.
     */
    private void sig2scope(Sig sig, int newValue) throws Err {
        if (sig.builtin)
            throw new ErrorSyntax(cmd.pos, "Cannot specify a scope for the builtin signature \"" + sig + "\"");
        if (!(sig instanceof PrimSig))
            throw new ErrorSyntax(cmd.pos, "Cannot specify a scope for a subset signature \"" + sig + "\"");
        if (newValue < 0)
            throw new ErrorSyntax(cmd.pos, "Cannot specify a negative scope for sig \"" + sig + "\"");
        int old = sig2scope(sig);
        //        if (old==newValue) return;
        //[VM] Not a good condition
        //        if (old>=0 && !hasLower(sig))        throw new ErrorSyntax(cmd.pos, "Sig \""+sig+"\" already has a scope of "+old+", so we cannot set it to be "+newValue);
        sig2scope.put((PrimSig) sig, newValue);
        rep.scope("Sig " + sig + " scope <= " + newValue + "\n");
    }

    /** Sets the upper-bound scope for a sig; returns true iff the sig's scope is changed by this call. */
    private void sig2PscopeU(Sig sig, List<String> newValue) throws Err {
        System.out.println("sig->"+sig+", newValue->"+newValue+", type->"+sig.getClass());
        if (sig.builtin)                throw new ErrorSyntax(cmd.pos, "Cannot specify a scope for the builtin signature \""+sig+"\"");
        if (!(sig instanceof PrimSig))  throw new ErrorSyntax(cmd.pos, "Cannot specify a scope for a subset signature \""+sig+"\"");
        if (newValue == null)                 throw new ErrorSyntax(cmd.pos, "Cannot specify a Null Partial scope for sig \""+sig+"\"");
        int old=sig2scope(sig);
        List<String> oldList = sig2PscopeU.get(sig);
        if (oldList != null && oldList.containsAll(newValue)) 
            return;
        //        if (old>=0)        throw new ErrorSyntax(cmd.pos, "Sig \""+sig+"\" already has a scope of "+old+", so we cannot set it to be "+newValue);
        sig2PscopeU.put(sig.label, newValue);
        rep.scope("Sig "+sig+" scope <= "+newValue+"\n");
    }
 
    /** Sets the upper-bound scope for a sig; returns true iff the sig's scope is changed by this call. */
    private void sig2PscopeL(Sig sig, List<String> newValue) throws Err {
        if (sig.builtin)                throw new ErrorSyntax(cmd.pos, "Cannot specify a scope for the builtin signature \""+sig+"\"");
        if (!(sig instanceof PrimSig))  throw new ErrorSyntax(cmd.pos, "Cannot specify a scope for a subset signature \""+sig+"\"");
        if (newValue == null)                 throw new ErrorSyntax(cmd.pos, "Cannot specify a Null Partial scope for sig \""+sig+"\"");
        int old=sig2scope(sig);
        List<String> oldList = sig2PscopeU.get(sig);
        if (oldList != null && oldList.containsAll(newValue)) return;
        //        if (old==newValue.size()) return;
        //        if (old>=0)        throw new ErrorSyntax(cmd.pos, "Sig \""+sig+"\" already has a scope of "+old+", so we cannot set it to be "+newValue);
        sig2PscopeL.put(sig.label, newValue);
        rep.scope("Sig "+sig+" scope <= "+newValue+"\n");
    }
 
    /** Sets the scope for a sig; returns true iff the sig's scope is changed by this call. */
    private void field2PscopeL(Sig sig, List<List<String>> newValue) throws Err {
        field2PscopeL(((PrimSig)sig).label, newValue);
    }
 
    /** Sets the scope for a sig; returns true iff the sig's scope is changed by this call. */
    private void field2PscopeL(String label, List<List<String>> newValue) throws Err {
        if (newValue == null)                 throw new ErrorSyntax(cmd.pos, "Cannot specify a Null Partial scope for field's label \""+label+"\"");
        int old = field2PscopeL(label)== null ? -1 : field2PscopeL(label).size();
        if (old==newValue.size()) return;
        if (old>=0)        throw new ErrorSyntax(cmd.pos, "Fields's label \""+label+"\" already has a scope of "+old+", so we cannot set it to be "+newValue);
        field2PscopeL.put(label, newValue);
        rep.scope("Filed's label "+label+" scope <= "+newValue+"\n");
    }
 
    /** Sets the scope for a sig; returns true iff the sig's scope is changed by this call. */
    private void field2PscopeU(Sig sig, List<List<String>> newValue) throws Err {
        field2PscopeU(((PrimSig)sig).label, newValue);
    }
 
    /** Sets the scope for a sig; returns true iff the sig's scope is changed by this call. */
    private void field2PscopeU(String label, List<List<String>> newValue) throws Err {
        if (newValue == null)                 throw new ErrorSyntax(cmd.pos, "Cannot specify a Null Partial scope for field's label \""+label+"\"");
        int old = field2PscopeU(label)== null ? -1 : field2PscopeU(label).size();
        if (old==newValue.size()) return;
        if (old>=0)        throw new ErrorSyntax(cmd.pos, "Fields's label \""+label+"\" already has a scope of "+old+", so we cannot set it to be "+newValue);
        field2PscopeU.put(label, newValue);
        rep.scope("Filed's label "+label+" scope <= "+newValue+"\n");
    }
    
    // TODO It is sloppy, but the filed is not field, so I need to think in a better way. 
    /** Returns whether the scope of a sig is exact or not. */
    public boolean isExact(String label) {
        for(Sig field: exact.keySet()){
            if(field.label.equals(label)){
                return true;
            }
        }
        return false;
    }

    /** Returns whether the scope of a sig is exact or not. */
    public boolean isExact(Sig sig) {
        return sig == SIGINT || sig == SEQIDX || sig == STRING || ((sig instanceof PrimSig) && exact.containsKey(sig));
    }

    /** There is extra integers in the Int's atom set. */
    public boolean hasExtraInteger(){
        return !exInt.isEmpty();
    }
 
    //TODO I don't know whether we need to check (sig instanceof PrimSig)
    /** Returns whether the scope of a sig is exact or not. */
    public boolean hasLower(String label) {
        for(Sig field: lower.keySet()){
            if(field.label.equals(label)){
                return true;
            }
        }
        return false;    
    }
 
    /** Returns whether the scope of a sig is exact or not. */
    public boolean hasLower(Sig sig) {
        return ((sig instanceof PrimSig) && lower.containsKey(sig));
    }
 
    /** Returns whether the scope of a sig is exact or not. */
    public boolean hasUpper(Sig sig) {
        return ((sig instanceof PrimSig) && upper.containsKey(sig));
    }
 
    //TODO I don't know whether we need to check (sig instanceof PrimSig)
    /** Returns whether the scope of a sig is exact or not. */
    public boolean hasUpper(String label) {
        for(Sig field: upper.keySet()){
            if(field.label.equals(label)){
                return true;
            }
        }
        return false;
    }

    /** Make the given sig "exact". */
    private void makeExact(Pos pos, Sig sig) throws Err {
        if (!(sig instanceof PrimSig))
            throw new ErrorSyntax(pos, "Cannot specify a scope for a subset signature \"" + sig + "\"");
        exact.put(sig, sig);
    }

    /** Make the given sig "lower bound". */
    private void makeLower(Pos pos, Sig sig) throws Err {
        //Do we need to have a prime number?!
        if (!(sig instanceof PrimSig)) throw new ErrorSyntax(pos, "Cannot specify a scope for a subset signature \""+sig+"\"");
        lower.put(sig, sig);
    }
 
    /** Make the given sig "lower bound". */
    private void makeUpper(Pos pos, Sig sig) throws Err {
        //Do we need to have a prime number?!
        if (!(sig instanceof PrimSig)) throw new ErrorSyntax(pos, "Cannot specify a scope for a subset signature \""+sig+"\"");
        upper.put(sig, sig);
    }

    /**
     * Modifies the integer bitwidth of this solution's model (and sets the max
     * sequence length to 0)
     */
    private void setBitwidth(Pos pos, int newBitwidth) throws ErrorAPI, ErrorSyntax {
        if (newBitwidth < 0)
            throw new ErrorSyntax(pos, "Cannot specify a bitwidth less than 0");
        if (newBitwidth > 30)
            throw new ErrorSyntax(pos, "Cannot specify a bitwidth greater than 30");
        bitwidth = newBitwidth;
        maxseq = 0;
        sig2scope.put(SIGINT, bitwidth < 1 ? 0 : 1 << bitwidth);
        sig2scope.put(SEQIDX, 0);
    }

    /** Modifies the maximum sequence length. */
    private void setMaxSeq(Pos pos, int newMaxSeq) throws ErrorAPI, ErrorSyntax {
        if (newMaxSeq > max())
            throw new ErrorSyntax(pos, "With integer bitwidth of " + bitwidth + ", you cannot have sequence length longer than " + max());
        if (newMaxSeq < 0)
            newMaxSeq = 0; // throw new ErrorSyntax(pos, "The maximum sequence
                          // length cannot be negative.");
        maxseq = newMaxSeq;
        sig2scope.put(SEQIDX, maxseq);
    }

    /** Returns the largest allowed integer. */
    private int max() {
        return Util.max(bitwidth);
    }

    /** Returns the smallest allowed integer. */
    private int min() {
        return Util.min(bitwidth);
    }

    // ===========================================================================================================================//

    /** Defining the new rule: A super-sig is abstract. */
    private boolean derive_abstract_scope_rule1 (Iterable<Sig> sigs) throws Err {
        for(Sig sig:sigs){
            derive_abstract_sig_bound(sig);
        }
        return false;
    }
 
    /* Complaining the concrete super-sig. super-sig should be abstract sig.*/
    private void check_abstract_hierchy(Iterable<Sig> sigs) throws Err{
        for(Sig sig:sigs){
            if((!sig.builtin) && (sig.isAbstract == null) &&
                    (sig instanceof PrimSig)){
                //[VM] If all children are abstract, no matter the parent is not abstract
                for(PrimSig c:((PrimSig)sig).children()){
                    if(c.isAbstract == null && !c.label.contains("~")){
                        throw new ErrorSyntax(sig.pos, "The super-sig must be an abstract.");
                    }
                }
            }
        }
    }
 
    /**It derives the the scope of an abstract sig, from its children. If it does not have a child, the bounds are empty.*/
    private void derive_abstract_sig_bound(Sig sig) throws Err{
        if(sig.isAbstract == null || sig.builtin)
            return;
 
        List<String> listL = new ArrayList<String>();
        List<String> listU = new ArrayList<String>();
 
        int sum=0;
        for(PrimSig c:((PrimSig)sig).children()){
            if(c.isAbstract != null)
                derive_abstract_sig_bound(c);
            if(sig2PScopeL(c) > 0)
                listL.addAll(sig2PscopeL(c));
            if(sig2PScopeU(c) > 0)
                listU.addAll(sig2PscopeU(c));
            if(sig2scope(c) > 0)
                sum = sum + sig2scope(c);
        }
        sig2PscopeL(sig, listL);
        sig2PscopeU(sig, listU);
        sig2scope(sig, sum);
    }

    /**
     * If A is abstract, unscoped, and all children are scoped, then set A's scope
     * to be the sum; if A is abstract, scoped, and every child except one is
     * scoped, then set that child's scope to be the difference.
     */
    private boolean derive_abstract_scope(Iterable<Sig> sigs) throws Err {
        boolean changed = false;
        again: for (Sig s : sigs)
            if (!s.builtin && (s instanceof PrimSig) && s.isAbstract != null) {
                List<String> listL = new ArrayList<String>();
                List<String> listU = new ArrayList<String>();
                SafeList<PrimSig> subs = ((PrimSig) s).children();
                if (subs.size() == 0)
                    continue;
                Sig missing = null;
                int sum = 0;
                for (Sig c : subs) {
                    int cn = sig2scope(c);
                    if (cn < 0) {
                        if (missing == null) {
                            missing = c;
                            continue;
                        } else {
                            continue again;
                        }
                    }
                    sum = sum + cn;
                    listL.addAll(sig2PscopeL(c));
                    listU.addAll(sig2PscopeU(c));
                    if (sum < 0)
                        throw new ErrorSyntax(cmd.pos, "The number of atoms exceeds the internal limit of " + Integer.MAX_VALUE);
                }
                int sn = sig2scope(s);
                if (sn < 0) {
                    if (missing != null)
                        continue;
                    sig2scope(s, sum);
                    changed = true;
                    //The else means that one or more sub-sigs does not have scope.
                    //It means that, The super-sig has already some atoms, one of its sub-sigs is not scoped, So, the scope of such sub-sig should be the rest.
                } else if (missing != null) {
                    sig2scope(missing, (sn < sum) ? 0 : sn - sum);
                    changed = true;
                }
            }
        return changed;
    }

    private List<String> nameRangeGen(Sig sig, int start, int length){
        List<String> list  = new ArrayList<String>();
        String name=sig.label;
        if (name.startsWith("this/")) 
            name=name.substring(5);
        StringBuilder sb=new StringBuilder();
        for(int i=start; i < length; i++) {
            String x = sb.delete(0, sb.length()).append(name).append('$').append(i).toString();
            list.add(x);
        }               
        return list;
    }
    //===========================================================================================================================//
 
    /**
     * In case of top-down approach, we need to set the upper-bound for each, unbound sig, and set the upper-bound for each sig having lower bound.
     * @throws Err 
     */
    private void derive_overall_scope_bound(Iterable<Sig> sigs) throws Err{
 
        final int overall = (cmd.overall<0 || cmd.scope.size()==0) ? 3 : cmd.overall;
        for(Sig sig:sigs) {
            //Checking to see if an atom is gotten accessed from appended fact.
            if(sig.label.contains("~")){
                List<String> listL = new ArrayList<String>();
                List<String> listU = new ArrayList<String>();
 
                //The atoms that are accessible by appended fact.
                listL.add(sig.label.replace('~', '%').substring("this/".length()));
                listU.add(sig.label.replace('~', '%').substring("this/".length()));
                sig2PscopeL(sig, listL);
                sig2PscopeU(sig, listU);
                sig2scope(sig, 1);
                continue;
            }
            if(!sig.builtin && sig.isAbstract == null ){
                int rest = 0;
                if(sig2PScopeL(sig) > 0 && hasLower(sig) && !hasUpper(sig)){
                    rest = overall - sig2PScopeL(sig);
                    if (sig2scope(sig) == overall)
                        continue;
                    if(rest > 0){
                        List<String> list = new ArrayList<String>();
                        list.addAll(sig2PscopeU(sig));
                        list.addAll(nameRangeGen(sig, 0, rest));
                        sig2PscopeU(sig,list);
                        sig2scope(sig, overall);
                    }
                }else if(sig2PScopeU(sig) < 0){
                    int u = sig2scope(sig) < 0 ? overall : sig2scope(sig);
                    sig2PscopeU(sig,nameRangeGen(sig, 0, u));
                    if(isExact(sig))
                        sig2PscopeL(sig,nameRangeGen(sig, 0, u));
                    else
                        sig2PscopeL(sig,new ArrayList<String>());
                    sig2scope(sig, u);                  
                }
            }
        }
    }

    // ===========================================================================================================================//

    /**
     * If A is toplevel, and we haven't been able to derive its scope yet, then let
     * it get the "overall" scope.
     */
    private boolean derive_overall_scope(Iterable<Sig> sigs) throws Err {
        boolean changed = false;
        final int overall = (cmd.overall < 0 && cmd.scope.size() == 0) ? 3 : cmd.overall;
        for (Sig s : sigs)
            // Insert the rest.
            if (!s.builtin && sig2PScopeL(s) > 0 && hasLower(s)) {
                int rest = overall - sig2PScopeL(s);
                if (sig2scope(s) == overall)
                    continue;
                if (rest > 0) {
                    sig2scope(s, overall);
                    changed=true;
                    continue;
                }
            }else
                if (!s.builtin && s.isTopLevel() && sig2scope(s)<0 && sig2PScopeL(s) < 0) {
                    if (s.isEnum!=null) { 
                        sig2scope(s, 0); 
                        continue; 
                    } // enum without children should get the empty set
                    if (overall<0) 
                        throw new ErrorSyntax(cmd.pos, "You must specify a scope for sig \"" + s + "\"");
                sig2scope(s, overall);
                changed = true;
            }
        return changed;
    }

    // ===========================================================================================================================//

    /**
     * If A is not toplevel, and we haven't been able to derive its scope yet, then
     * give it its parent's scope.
     */
    private boolean derive_scope_from_parent(Iterable<Sig> sigs) throws Err {
        boolean changed = false;
        Sig trouble = null;
        for (Sig s : sigs)
            if (!s.builtin && !s.isTopLevel() && sig2scope(s) < 0 && sig2PScopeL(s) < 0 && (s instanceof PrimSig)) {
                PrimSig p = ((PrimSig) s).parent;
                int pb = sig2scope(p);
                if (pb >= 0) {
                    sig2scope(s, pb);
                    changed = true;
                } else {
                    trouble = s;
                }
            }
        if (changed)
            return true;
        if (trouble == null)
            return false;
        throw new ErrorSyntax(cmd.pos, "You must specify a scope for sig \"" + trouble + "\"");
    }

    // ===========================================================================================================================//

    /**
     * Regarding the bottom-up approach, we are ony traversing the Upper-bound list and put the tokens in the atom list.
     */
    private void makeAtoms(final PrimSig sig){
        if (sig.builtin) return;
        List<String> list = sig2PscopeU(sig);
        if(list != null){
            this.atoms.addAll(list);
        }
    }

    // ===========================================================================================================================//

    /**
     * Computes the number of atoms needed for each sig (and add these atoms to
     * this.atoms)
     */
    private int computeLowerBound(final PrimSig sig) throws Err {
        if (sig.builtin)
            return 0;
        int n = sig2scope(sig), lower = 0;
        boolean isExact = isExact(sig);
        // First, figure out what atoms *MUST* be in this sig
        for (PrimSig c : sig.children())
            lower = lower + computeLowerBound(c);
        // Bump up the scope if the sum of children exceed the scope for this
        // sig
        if (n < lower) {
            if (isExact)
                rep.scope("Sig " + sig + " scope raised from ==" + n + " to be ==" + lower + "\n");
            else
                rep.scope("Sig " + sig + " scope raised from <=" + n + " to be <=" + lower + "\n");
            n = lower;
            sig2scope.put(sig, n);
        }
        // Add special overrides for "exactly" sigs
        if (!isExact && cmd.additionalExactScopes.contains(sig)) {
            isExact = true;
            rep.scope("Sig " + sig + " forced to have exactly " + n + " atoms.\n");
            makeExact(Pos.UNKNOWN, sig);
        }
        //[VM] 
        StringBuilder sb2=new StringBuilder();
        if (sig2PscopeL.containsKey(sig.label)) {
            for (String str: sig2PscopeL.get(sig.label)) {
                if (str.startsWith("this/")) 
                    str=str.substring(5);
                str=un.make(str);
                atoms.add(sb2.delete(0, sb2.length()).append(str).append('%').toString());
                lower++;
            }
            int rest = sig2scope.get(sig) != null ? sig2scope.get(sig) : lower;
 
            if ( rest > lower) {
                String name=sig.label;
                if (name.startsWith("this/")) 
                    name=name.substring(5);
                StringBuilder sb=new StringBuilder();
                for (int i=0; i<(rest-lower)+1; i++) {
                    String x = sb.delete(0, sb.length()).append(name).append('$').append(i).toString();
                    atoms.add(x);
                    lower++;
                }
            }
        }
        // Create atoms
        if (n > lower && (isExact || sig.isTopLevel())) {
            // Figure out how many new atoms to make
            n = n - lower;
            // Pick a name for them
            String name = sig.label;
            if (name.startsWith("this/"))
                name = name.substring(5);
            name = un.make(name);
            // Now, generate each atom using the format "SIGNAME$INDEX"
            // By prepending the index with 0 so that they're the same width, we
            // ensure they sort lexicographically.
            StringBuilder sb = new StringBuilder();
            for (int i = 0; i < n; i++) {
                String x = sb.delete(0, sb.length()).append(name).append('$').append(i).toString();
                atoms.add(x);
                lower++;
            }
        }
        return lower;
    }

    // ===========================================================================================================================//

    /**
     * Compute the scopes, based on the settings in the "cmd", then log messages to
     * the reporter.
     */
    private ScopeComputer(A4Reporter rep, Iterable<Sig> sigs, Command cmd) throws Err {
        this.rep = rep;
        this.cmd = cmd;
        boolean shouldUseInts = true; // TODO CompUtil.areIntsUsed(sigs, cmd);
        // Process each sig listed in the command
        for (CommandScope entry : cmd.scope) {
            Sig s = entry.sig;
            int scope = entry.startingScope;
            boolean exact = entry.isExact;
            boolean lower = entry.hasLower;
            boolean upper = entry.hasUpper;
            if (s == UNIV)
                throw new ErrorSyntax(cmd.pos, "You cannot set a scope on \"univ\".");
            if (s == SIGINT)
                throw new ErrorSyntax(cmd.pos, "You can no longer set a scope on \"Int\". " + "The number of atoms in Int is always exactly equal to 2^(i" + "nteger bitwidth).\n");
            if (s == SEQIDX)
                throw new ErrorSyntax(cmd.pos, "You cannot set a scope on \"seq/Int\". " + "To set the maximum allowed sequence length, use the seq keyword.\n");
            if (s == STRING) {
                if (maxstring >= 0)
                    throw new ErrorSyntax(cmd.pos, "Sig \"String\" already has a scope of " + maxstring + ", so we cannot set it to be " + scope);
                if (!exact)
                    throw new ErrorSyntax(cmd.pos, "Sig \"String\" must have an exact scope.");
                maxstring = scope;
                continue;
            }
            if (s == NONE)
                throw new ErrorSyntax(cmd.pos, "You cannot set a scope on \"none\".");
            if (s.isEnum != null)
                throw new ErrorSyntax(cmd.pos, "You cannot set a scope on the enum \"" + s.label + "\"");
            if (s.isOne != null && scope != 1)
                throw new ErrorSyntax(cmd.pos, "Sig \"" + s + "\" has the multiplicity of \"one\", so its scope must be 1, and cannot be " + scope);
            if (s.isLone != null && scope > 1)
                throw new ErrorSyntax(cmd.pos, "Sig \"" + s + "\" has the multiplicity of \"lone\", so its scope must 0 or 1, and cannot be " + scope);
            if (s.isSome != null && scope < 1)
                throw new ErrorSyntax(cmd.pos, "Sig \"" + s + "\" has the multiplicity of \"some\", so its scope must 1 or above, and cannot be " + scope);
            if (entry.isPartial) {
                if (entry.pFields.size() > 0) {
                    List<List<String>> listL = new ArrayList<List<String>>();
                    List<List<String>> listU = new ArrayList<List<String>>();
                    int i = 0;
                    for (List<Expr> pair: entry.pFields ) {
                        List<String> tmp = new ArrayList<String>();
                        for (Expr ev: pair)
                            if (ev instanceof ExprVar)
                                //Here the Sig in relation can be extended.
                                tmp.add(((ExprVar)ev).label+"%");
                            else if (ev instanceof ExprConstant ){
                                tmp.add(String.valueOf(((ExprConstant)ev).num));
                                //[VM] putting the mentioned integer inside the set, later out of the range values are added in the universe
                                exInt.add(((ExprConstant)ev).num);      
                            }
                        if (i<entry.pAtomsLowerLastIndex)
                            listL.add(tmp);
                        else
                            listU.add(tmp);
                        i++;
                    }
                    listU.addAll(0, listL);
                    field2PscopeL(s,listL);
                    field2PscopeU(s,listU);
                }else{
                    List<String> listL = new ArrayList<String>();
                    List<String> listU = new ArrayList<String>();
                    int i = 0;
                    for (Expr var: entry.pAtoms) {
                        if (var instanceof ExprVar) {
                            if (i < entry.pAtomsLowerLastIndex)
                                listL.add(((ExprVar)var).label+"%");
                            else
                                listU.add(((ExprVar)var).label+"%");
                        }
                        else if (var instanceof ExprConstant ) {
                            //[VM] It is not possible to have an Singlton Int, but just in case it is stored.
                            exInt.add(((ExprConstant)var).num);     
                            if (i < entry.pAtomsLowerLastIndex){
                                listL.add(String.valueOf(((ExprConstant)var).num));
                            }else {
                                listU.add(String.valueOf(((ExprConstant)var).num));
                            }
                        }
                        i++;
                    }
                    listU.addAll(0, listL);
                    //Upper-bound and lower-bound are the same.
                    sig2PscopeU(s,listU);
                    sig2PscopeL(s,listL);
                    //sig2scope stores the upper-bound for back-ward compatibility. In case of other use case, 
                    //other methods can be called to read the size from maps directly. 
                    sig2scope(s, listU.size());
                }
 
            }else{
                sig2scope(s, scope);
            }
            if (exact)
                makeExact(cmd.pos, s);
            if (lower)
                makeLower(cmd.pos, s);
            if (upper)
                makeUpper(cmd.pos, s);

        }
        // Force "one" sigs to be exactly one, and "lone" to be at most one
        for (Sig s : sigs)
            if (s instanceof PrimSig) {
                if (s.isOne != null) {
                    makeExact(cmd.pos, s);
                    sig2scope(s, 1);
                } else if (s.isLone != null && sig2scope(s) != 0)
                    sig2scope(s, 1);
            }

        //Generate all atoms for concrete sigs.
        derive_overall_scope_bound(sigs);
 
        //[VM] Derive scopes for abstract sigs, The super-sigs should be only abstract.
        // Complaint about the concrete super-sig. super-sig should be abstract sig.
        check_abstract_hierchy(sigs);
        derive_abstract_scope_rule1(sigs);
        
        // Derive the implicit scopes
        /*while(true) {
            if (derive_abstract_scope(sigs))    { do {} while(derive_abstract_scope(sigs));     continue; }
            if (derive_overall_scope(sigs))     { do {} while(derive_overall_scope(sigs));      continue; }
            //[VM]We do not evaluating in top-down approach yet.
            if (derive_scope_from_parent(sigs)) { do {} while(derive_scope_from_parent(sigs));  continue; }
            break;
        }*/
        // Set the initial scope on "int" and "Int" and "seq"
        int maxseq = cmd.maxseq, bitwidth = cmd.bitwidth;
        if (bitwidth < 0) {
            bitwidth = (shouldUseInts ? 4 : 0);
        }
        setBitwidth(cmd.pos, bitwidth);
        if (maxseq < 0) {
            if (cmd.overall >= 0)
                maxseq = cmd.overall;
            else
                maxseq = 4;
            int max = Util.max(bitwidth);
            if (maxseq > max)
                maxseq = max;
        }
        setMaxSeq(cmd.pos, maxseq);
        // Generate the atoms and the universe
        for (Sig s : sigs)
            if (s.isTopLevel())
                //[VM] To make and top-down apprach
                //computeLowerBound((PrimSig)s);
                makeAtoms((PrimSig)s);
        int max = max(), min = min();
        if (max >= min)
            for (int i=min; i<=max; i++) 
                atoms.add(""+i);
        //[VM] First, check if the user set the sparse value to true
        for (Integer i: exInt) {
            if (i >=min && i <= max) {
                exInt.remove(i);
            }else{
                atoms.add(String.valueOf(i));
            }
        }

    }

    // ===========================================================================================================================//

    /**
     * Computes the scopes for each sig and computes the bitwidth and maximum
     * sequence length.
     * <p>
     * The scopes are determined as follows:
     * <p>
     * "run x": every topsig is scoped to <= 3 elements.
     * <p>
     * "run x for N": every topsig is scoped to <= N elements.
     * <p>
     * "run x for N but N1 SIG1, N2 SIG2...": <br>
     * Every sig following "but" is constrained explicitly. <br>
     * Any topsig that is <br>
     * a) not listed, and <br>
     * b) its scope is not derived otherwise <br>
     * will be scoped to have <= N elements.
     * <p>
     * "run x for N1 SIG1, N2 SIG2..." <br>
     * Every sig following "but" is constrained explicitly. <br>
     * Any topsig that is <br>
     * a) not listed, and <br>
     * b) its scope is not derived otherwise <br>
     * we will give an error message.
     * <p>
     * Please see ScopeComputer.java for the exact rules for deriving the missing
     * scopes.
     */
    static Pair<A4Solution,ScopeComputer> compute(A4Reporter rep, A4Options opt, Iterable<Sig> sigs, Command cmd) throws Err {
        ScopeComputer sc = new ScopeComputer(rep, sigs, cmd);
        Set<String> set = cmd.getAllStringConstants(sigs);
        if (sc.maxstring >= 0 && set.size() > sc.maxstring)
            rep.scope("Sig String expanded to contain all " + set.size() + " String constant(s) referenced by this command.\n");
        for (int i = 0; set.size() < sc.maxstring; i++)
            set.add("\"String" + i + "\"");
        sc.atoms.addAll(set);
        A4Solution sol = new A4Solution(cmd.toString(), sc.bitwidth, sc.maxseq, set, sc.atoms, rep, opt, cmd.expects);
        return new Pair<A4Solution,ScopeComputer>(sol, sc);
    }
}
