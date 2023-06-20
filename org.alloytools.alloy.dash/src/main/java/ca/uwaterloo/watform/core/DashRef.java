/*
	These static methods let us treat an Expr as a reference to a Dash object
	that has a name and a list of parameter values.

	From Root/A/B[exp1,exp2]/v1 in parsing
	a DashRef is recorded in the AST as $$PROCESSREF$$ . exp2 . exp1 . Root/A/B/v1

	After resolving, a DashRef with no params is $$PROCESSREF$$. var1

	These references can be within Alloy Expr so we can't do a class extension.

	Even though we could do something different for states/events 
	(where they aren't referenced within Expr)
	its best to use the same functions for all

	Note: we cannot allow any of
	b1 -> a1 -> var1
	b1.a1.var1
	var1[a1,b1]
	as a way to reference vars or events with parameter values b/c we cannot
	tell the difference between the above and something like Chairs.occupied'
	where "Chairs" is not a parameter value but a something to be joined with
	occupied after it has all of its parameter values.
*/

package ca.uwaterloo.watform.core;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.JoinableList;
import edu.mit.csail.sdg.ast.Browsable;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.Type;
import edu.mit.csail.sdg.ast.VisitReturn;


import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

import java.util.List;
import java.util.ArrayList;
//import java.util.JoinableList;

import edu.mit.csail.sdg.alloy4.Pos;
//import edu.mit.csail.sdg.alloy4.ErrorWarning;
//import edu.mit.csail.sdg.alloy4.Err;
//import edu.mit.csail.sdg.ast.Type;
//import edu.mit.csail.sdg.ast.Browsable;
//import edu.mit.csail.sdg.ast.VisitReturn;
import edu.mit.csail.sdg.ast.Expr;
//import edu.mit.csail.sdg.ast.ExprBinary;
//import edu.mit.csail.sdg.ast.ExprVar;

import static ca.uwaterloo.watform.alloyasthelper.ExprHelper.*;
import ca.uwaterloo.watform.core.DashUtilFcns;
import ca.uwaterloo.watform.core.DashErrors;
import ca.uwaterloo.watform.core.DashRef;

public class DashRef extends Expr {

	//private Pos pos;
	private DashRefKind kind;
	private String name;
	private List<Expr> paramValues;

	// generally in the code we know the kind by context but
	// for printing we need the kind here
	// and this simplified some code for the DashRef to know its kind
	private static enum DashRefKind {
		STATE,
		EVENT,
		VAR,
		TRANS
		// BUFFER ????
	}

	// for internal uses
	public DashRef(DashRefKind k, String n, List<Expr> prmValues) {
		super(Pos.UNKNOWN, Type.FORMULA);
		this.kind = k;
		this.name = n;
		this.paramValues = prmValues;
		//List<Expr> ll = new ArrayList<Expr>(eList);
		//Collections.reverse(ll);
		//ll.add(createVar(n));
		//return createJoin(processRef(), createJoinList(ll));		
	}

	// for uses in parsing
	public DashRef(Pos p, DashRefKind k, String n, List<Expr> prmValues) {
		super(p, Type.FORMULA);
		this.kind = k;
		this.name = n;
		this.paramValues = prmValues;
		//List<Expr> ll = new ArrayList<Expr>(eList);
		//Collections.reverse(ll);
		//ll.add(createVar(n));
		//return createJoin(processRef(), createJoinList(ll));		
	}

	public static DashRef createStateDashRef(Pos p, String n, List<Expr> prmValues) {
		return new DashRef(p, DashRefKind.STATE,n, prmValues);
	}
	public static DashRef createEventDashRef(Pos p, String n, List<Expr> prmValues) {
		return new DashRef(p, DashRefKind.EVENT,n, prmValues);
		
	}
	public static DashRef createVarDashRef(Pos p, String n, List<Expr> prmValues) {
		return new DashRef(p, DashRefKind.VAR,n, prmValues);
	}
	public static DashRef createStateDashRef(String n, List<Expr> prmValues) {
		return new DashRef(DashRefKind.STATE,n, prmValues);
	}
	public static DashRef createEventDashRef(String n, List<Expr> prmValues) {
		return new DashRef(DashRefKind.EVENT,n, prmValues);
		
	}
	public static DashRef createVarDashRef(String n, List<Expr> prmValues) {
		return new DashRef(DashRefKind.VAR,n, prmValues);
	}
	public static DashRef createTransDashRef(String n, List<Expr> prmValues) {
		return new DashRef(DashRefKind.TRANS,n, prmValues);
		
	}

	/*
	public static Expr createDashRef(Pos p, String n, List<Expr> eList) {
		List<Expr> ll = new ArrayList<Expr>(eList);
		Collections.reverse(ll);
		ll.add(createVar(p, n));
		return createJoin(p, processRef(), createJoinList(ll));		
	}
	*/
	public static List<Expr> emptyParamValuesList() {
		return new ArrayList<Expr>();
	}

	// we probably don't need this anymore
	/*
	private static Expr processRef() {
		return createVar(DashStrings.processRef);
	}
	*/

	public static boolean isDashRef(Expr r) {
		return (r instanceof DashRef);
		/*
		if (isExprJoin(e)) 
			if (isExprVar(getLeft(e)))
				return sEquals(getLeft(e), processRef());
		return false;
		*/
	}
	public String getName() {
		return name;
	}
	public List<Expr> getParamValues() {
		return paramValues;
	}
	public boolean isState() {
		return kind == DashRefKind.STATE;
	}
	public boolean isEvent() {
		return kind == DashRefKind.EVENT;
	}
	public boolean isVar() {
		return kind == DashRefKind.EVENT;
	}
	//public Pos getPos() {
	//	return pos;
	//}
	
	public String toString() {
		// STATE: Root/A/B[a1,b1]
		// other: Root/A/B[a1,b1]/var1
		String s = "";
		if (kind == DashRefKind.STATE) {
			s += getName();
		} else {
			// might not yet have a prefix
			if (DashFQN.isFQN(getName()))
				s += DashFQN.chopPrefixFromFQN(getName());
			else
				s += "NoPrefixYet";
		}
        
        if (!paramValues.isEmpty()) {
        	s += "[";
	        List<String> paramValues = 
	            getParamValues().stream()
	            .map(i -> i.toString())
	            .collect(Collectors.toList());
	        //Collections.reverse(paramValues);
	        s += DashUtilFcns.strCommaList(paramValues);
	        s += "]";
	    }
        if (kind != DashRefKind.STATE) {
        	s += "/";
        	s += DashFQN.chopNameFromFQN(getName());
        }
        return s;
	}
	
   /** {@inheritDoc} */
    @Override
    public void toString(StringBuilder out, int indent) {
    	// STATE: Root/A/B[a1,b1]
		// other: Root/A/B[a1,b1]/var1
		String s = "";
		if (kind == DashRefKind.STATE) {
			out.append(getName());
		} else {
			if (DashFQN.isFQN(getName()))
				out.append(DashFQN.chopPrefixFromFQN(getName()));
			else
				out.append("NoPrefixYet");
		}
        if (!paramValues.isEmpty()) {
        	out.append("[");
	        List<String> paramValues = 
		            getParamValues().stream()
		            .map(i -> i.toString())
		            .collect(Collectors.toList());
		        //Collections.reverse(paramValues);
		        out.append(DashUtilFcns.strCommaList(paramValues));
		        out.append("]");
		}
        if (kind != DashRefKind.STATE) {
        	out.append("/");
        	out.append(DashFQN.chopNameFromFQN(getName()));
        }
    }

    //TODO: fix below this line as these are methods
    // that must be present to inherit from Expr
    // but not sure what they should do
    // or if it is okay to have them do nothing
    // because DashRefs disappear in conversion to Alloy
	/** {@inheritDoc} */
    @Override
    public int getDepth() {
        int max = 1;
        for (Expr x : paramValues) {
            int tmp = x.getDepth();
            if (max < tmp)
                max = tmp;
        }
        return 1 + max;
    }
/** {@inheritDoc} */
    @Override
    public Expr resolve(Type p, Collection<ErrorWarning> warns) {
    	// this is not needed because DashRef disappear before
    	// Alloy resolve
    	return createNone();
   	}
   	/** {@inheritDoc} */
    @Override
    public final <T> T accept(VisitReturn<T> visitor) throws Err {
        return null;
    }
    /** {@inheritDoc} */
    @Override
    public List< ? extends Browsable> getSubnodes() {
        //Browsable a = make(var.pos, var.pos, "<b>var</b> " + var.label + " = ...", expr);
        //Browsable b = make(sub.span(), sub.span(), "<b>where...</b>", sub);
        return null;
    }
    /** {@inheritDoc} */
    @Override
    public String getHTML() {
        return "";
    }
	/*
	public static String getName(Expr e) {
		assert(isDashRef(e) || isExprVar(e));
		if (isDashRef(e)) {
			// might be a $$PROCESSREF$$.a.b.PRIME(e)
			while (isExprJoin(e)) e = getRight(e);
			assert(isExprVar(e));
		}
		return getVarName((ExprVar) e);
	}
	public static List<Expr> getParamValues(Expr e) {
		assert(isDashRef(e) || isExprVar(e));
		List<Expr> plist = new ArrayList<Expr>();
		// strip off $$PROCESSREF$$
		if (isDashRef(e)) {
			Expr f = getRight(e);
			while (isExprJoin(f)) {
				//System.out.println(f.toString());
				plist.add(getLeft(f));
				f = getRight(f);
			}
		}
		return plist;
	}
	*/
	/*
	public static Expr subForDashRefArrow(Expr e, Expr r) {
		if (isExprVar(e)) return r;
		else return createArrow(getLeft(e), subForDashRefArrow(getRight(e),r));
	}
	// works for Join or BadJoin
	public static Expr subForDashRefJoin(Expr e, Expr r) {
		if (isExprVar(e)) return r;
		else return createJoin(getLeft(e), subForDashRefJoin(getRight(e),r));
	}
	*/
	/*
	public Expr convertToJoin() {
		List<Expr> ll = new ArrayList<Expr>(getParamValues());
		//Collections.reverse(ll);
		ll.add(createVar(name));
		return createJoinList(ll);		
	}
	public Expr convertToArrow() {
		List<Expr> ll = new ArrayList<Expr>(getParamValues());
		//Collections.reverse(ll);
		ll.add(createVar(name));
		return createArrowExprList(ll);
	}
	*/
	/*
	private static Expr convertDashRefToArrowAux(Expr e) {
		//if (isExprVar(e)) return createVar(DashFQN.fqn(getVarName((ExprVar) e)));
		//else return createArrow(getLeft(e), convertDashRefToArrowAux(getRight(e)));
	}
	*/
	/*
	public static Expr convertDashRefToArrow(Expr e) {
		// removes $$PROCESSREF$$ and replaces joins with arrows
		Expr e1 = getRight(e);
		return convertDashRefToArrowAux(e1);
	}
	*/


	/*
	private Pos pos;
	private String name;
	private List<Expr> paramValues;

	public DashRef(Pos p, String n, List<Expr> eList) {
		this.pos = p;
		this.name = n;
		assert(n != null);
		assert(!n.isEmpty());
		assert(eList != null);
		this.paramValues = eList;
	}

	public DashRef(String n, List<Expr> eList) {
		this.pos = Pos.UNKNOWN;
		this.name = n;
		this.paramValues = eList;
		//System.out.println(n);
		//System.out.println(eList);
	}
	*/

	/*
	public String getName() {
		return name;
	}
	public List<Expr> getParamValues() {
		return paramValues;
	}
	public String toString() {
		String r = "";
		r += name + "[" + DashUtilFcns.strCommaList(paramValues) +"]";
		return r;
	}
	*/



	/*
		can only be used in an action
		exp2. exp1. Root/A/B/v1 or
		exp2. exp1. Root/A/B/v1'
	*/
	/*
	public static boolean isDashRefJoin(Expr e) {
		if (isExprJoin(e)) {
			Expr e2 = e;
			while (isExprJoin(e2)) e2 = getRight(e2);
			if (isExprVar(e2)) return true;
				//String v = getVarName((ExprVar)e2);
				//if (DashFQN.isFQN(v)) return true;
			//}
		}
		return false;
	}
	*/
	// results from pred calls Tk[xx]
	/*
	public static boolean isDashRefBadJoin(Expr e) {
		//System.out.println(e);
		//System.out.println(e.getClass().getName());
		if (isExprBadJoin(e)) {
			Expr e2 = e;
			while (isExprBadJoin(e2)) {
				e2 = getRight(e2);
			}
			if (isExprVar(e2)) return true; //{
				//String v = getVarName((ExprVar)e2);
				//if (DashFQN.isFQN(v)) return true;
			//}
		}
		return false;
	}
	*/
	/* 
		can only be used in an event
		exp2 -> exp1 -> Root/A/B/ev1 
	*/
	/*
	public static boolean isDashRefArrow(Expr e) {
		if (isExprArrow(e)) {
			Expr e2 = e;
			while (isExprArrow(e2)) e2 = getRight(e2);
			if (isExprVar(e2)) return true; //{
				//String v = getVarName((ExprVar)e2);
				//if (DashFQN.isFQN(v)) return true;
			//}
		}
		return false;
	}
	*/
	/*
		from exp2. exp2. Root/A/B/v1' return Root/A/B/v1'
	*/

	/*
		replaceDashRefExprVar(exp2. exp1. Root/A/B/v1', sNext.Root/A/B/v1 )
		returns exp2.exp1.sNext.Root/A/B/v1
	*/


	
    // referencing a for loop variable in a filter does not work
    // so do this as a loop
    public static List<DashRef> hasNumParams(List<DashRef> dr, int i) {
        // filter to ones that have this number of params
        //System.out.println(i);
        //System.out.println(dr);
        List<DashRef> o = dr.stream()
            .filter(x -> x.getParamValues().size() == i)
            .collect(Collectors.toList()); 
        //System.out.println(o);
        return o;
    }
    
}