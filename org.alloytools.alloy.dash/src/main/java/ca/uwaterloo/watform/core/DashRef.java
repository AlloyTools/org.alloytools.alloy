package ca.uwaterloo.watform.core;

import java.util.List;
import java.util.ArrayList;
import java.util.Collections;
import java.util.stream.Collectors;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprVar;

import static ca.uwaterloo.watform.alloyasthelper.ExprHelper.*;
import ca.uwaterloo.watform.core.DashUtilFcns;
import ca.uwaterloo.watform.core.DashErrors;
import ca.uwaterloo.watform.core.DashRef;

public class DashRef{
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

	// within expressions we can't have DashRefs
	// so we'll fake it
	public static Expr DashRefExpr(String n, List<Expr> eList) {
		// a lot like toAlloy
		List<Expr> ll = new ArrayList<Expr>(eList);
		Collections.reverse(ll);
		ll.add(createVar(n));
		//System.out.println(ll);
		//System.out.println(createJoin(processRef(), createJoinList(ll)));
		return createJoin(processRef(), createJoinList(ll));		
	}
	
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
	public static List<Expr> emptyParamValuesList() {
		return new ArrayList<Expr>();
	}



	// the following operations are about Alloy expressions that
	// represent joins from a DashRefs

	// These are:
	// exp2. exp1. Root/A/B/v1 (from Root/A/B[exp1,exp2]/v1 with Joins for events and vars in exp)
	// exp2. exp1. Root/A/B/v1 (with regular Joins for vars)
	// exp2 -> exp1 -> Root/A/B/v1 (from events)
	// We think it is a DashRef is there is a slash in the "name"
	// slashes aren't regularly allowed in Alloy

	// stuck in the formula the parser produces
	// from Root/A/B[exp1,exp2]/v1
	public static Expr processRef() {
		return createVar(DashStrings.processRef);
	}

	/* 
		could be used in an action or in an event expr 
		was built by new Expr rule in parser
		Root/A/B[exp1,exp2]/v1 is recorded in the AST as
		$$PROCESSREF$$ . exp2 . exp1 . Root/A/B/v1
	*/
	public static boolean isDashRefProcessRef(Expr e) {
		//System.out.println("in isDashRefProcessRef"+ e.toString());
		if (isExprJoin(e)) 
			if (isExprVar(getLeft(e)))
				return sEquals(getLeft(e), processRef());
		return false;
	}
	public static Expr getDashRefProcessRefVar(Expr e) {
		assert(isDashRefProcessRef(e));
		while (isExprJoin(e)) e = getRight(e);
		// might be a $$PROCESSREF$$.a.b.PRIME(e)
		return e;
	}
	public static List<Expr> getDashRefProcessRefParamValues(Expr e) {
		assert(isDashRefProcessRef(e));
		List<Expr> plist = new ArrayList<Expr>();
		// strip off $$PROCESSREF$$
		Expr f = getRight(e);
		while (isExprJoin(f)) {
			//System.out.println(f.toString());
			plist.add(getLeft(f));
			f = getRight(f);
		}
		return plist;
	}
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
	public static String nameOfDashRefExpr(Expr e) {
		//assert(isDashRefProcessRef(e) || isDashRefJoin(e) || isDashRefArrow(e) || isDashRefBadJoin(e));
		Expr e2 = getRight(e);
		while (/*isExprBadJoin(e2) ||*/ isExprJoin(e2)) {
			e2 = getRight(e2);
		}
		assert(isExprVar(e2));
		String v = getVarName((ExprVar) e2);
		//assert(DashFQN.isFQN(v));
		return v;
	}
	public static List<Expr> paramValuesOfDashRefExpr(Expr e) {
		List<Expr> r = new ArrayList<Expr>();
		Expr e1 = e;
		if (isDashRefProcessRef(e1)) {
			e1 = getRight(e1); // ignore $$PROCESSREF$$
			while (isExprJoin(e1)) {
				r.add(getLeft(e1));
				e1 = getRight(e1);
			}
		} /* else if (isExprJoin(e1)) {
			while (isExprJoin(e1)) {
				r.add(getLeft(e1));
				e1 = getRight(e1);
			}			
		} else if (isExprBadJoin(e1)) {
			while (isExprBadJoin(e1)) {
				r.add(getLeft(e1));
				e1 = getRight(e1);
			}	
		} else if (isExprArrow(e1)) {
			while (isExprArrow(e1)) {
				r.add(getLeft(e1));
				e1 = getRight(e1);
			}
		} */ else {
			DashErrors.nonDashRefExpr();
			return null;
		}
		return r;
	}
	/*
		replaceDashRefExprVar(exp2. exp1. Root/A/B/v1', sNext.Root/A/B/v1 )
		returns exp2.exp1.sNext.Root/A/B/v1
	*/

	public static Expr subForDashRefArrow(Expr e, Expr r) {
		if (isExprVar(e)) return r;
		else return createArrow(getLeft(e), subForDashRefArrow(getRight(e),r));
	}
	// works for Join or BadJoin
	public static Expr subForDashRefJoin(Expr e, Expr r) {
		if (isExprVar(e)) return r;
		else return createJoin(getLeft(e), subForDashRefJoin(getRight(e),r));
	}
	public static Expr convertDashRefProcessRefToArrow(Expr e) {
		// removes $$PROCESSREF$$ and replaces joins with arrows
		Expr e1 = getRight(e);
		return convertDashRefProcessRefToArrowAux(e1);
	}
	public static Expr convertDashRefProcessRefToArrowAux(Expr e) {
		if (isExprVar(e)) return fqnVar(e);
		else return createArrow(getLeft(e), convertDashRefProcessRefToArrowAux(getRight(e)));
	}	
	public static ExprVar fqnVar(Expr e) {
		assert(isExprVar(e));
		return createVar(DashFQN.fqn(getVarName((ExprVar) e)));
	}
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