package ca.uwaterloo.watform.ast;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

public class DashExpr  extends Dash {
	/* a wrapper around an Alloy Expr */

	private Expr ae;

	public DashExpr(Pos pos,Expr a) {
		this.pos = pos;
		this.ae = a;

	}

    public String toString() {
    	return ae.toString(); 
    }
    /*
	private Expr recurseResolveAll(Expr e, Set<String> ignore, String pth, symbolTable) {
		// replace var names by FQNs
		// replace "this" with ...
		// replace buffers with ...

		// do not need to record params b/c that will be in SymbolTable
		// ignore is the set of bound variables

		if (e isinstance ExprVar) {
			if (not (ignore.contains(e.label)) {
				if e.label.endsWith(DashStrings.PRIME) String x = e.label.substring(0,e.label.size()-1);
				else String x = e.label;
				if (!isFQN(x)) {
					// replace var with FQN
					//NAD we are assuming that it has a no type
					if e.label.endsWith(DashStrings.PRIME) Expr exp = createVar(fqn(pth,x) + DashStrings.PRIME)
					else exp =  createVar(fqn(pth + e.label.substring(0,e.label.size()-1)));
				} 
				symbolTable.addUsed(x);
				return exp;
			} else return e;
		} else if (e isinstance ExprUnary) {
			return e.op.make(recurseResolveAll(e.sub, ignore,pth));
		} else if (e isinstance ExprBinary) {
			Expr left = recurseResolveAll(e.left,ignore,pth);
			Expr right = recurseResolveAll(e.right,ignore,path);
			return e.op.make(left,right);
		} else if (e isinstance ExprITE) {
			Expr cond = recurseResolveAll(e.cond,ignore,pth);
			Expr left = recurseResolveAll(e.left,ignore,pth);
			Expr right = recurseResolveAll(e.right,ignore,path);
			return createITE(cond,left,right);
		} else if (e isinstance ExprQT) {
			Set<String> ig = new HashSet<String>();
			for (d: e.decls) for (x: d.names) ig.all(x.label);
			Expr sub = recurseResolveAll(e.sub, ignore.addAll(ig),pth);
			return createExprQT(e.op,e.decls,sub);
		} else {
			// expr type not yet covered in code
		}
	}

	public Expr resolveAll(String pth, symbolTable) {
		return DashExpr(recurseResolveAll(ae,emptySet(),pth));
	}

	private Set<DashDynSymbol> recurseGetDynamicSymbols(Expr e, Set<String> ignore) {
		// ignore is the set of bound variables
		if (e isinstance ExprVar && not(ignore.contains(e.label)) {
			if e.label.endsWith(DashStrings.PRIME) {
				Set<String> hs = new HashSet<String>()
				return hs.add(e)
			} else return emtpySet();
		} else if (e isinstance ExprUnary) {
			return recurseGetDynamicSymbols(e.sub, ignore)
		} else if (e isinstance ExprBinary) {
			return recurseGetDynamicSymbols(e.left,ignore).addAll(recurseGetDynamicSymbols(e.right, ignore))
		} else if (e isinstance ExprITE) {
			return recurseGetDynamicSymbols(e.left,ignore).addAll(recurseGetDynamicSymbols(e.right.ignore)).addAll(recurseGetDynamicSymbols(e.cond,ignore))
		} else if (e isinstance ExprQT) {
			Set<String> ig = new HashSet<String>();
			for (d: e.decls) for (x: d.names) ig.all(x.label)
			return recurseGetDynamicSymbols(e.sub,ignore.addAll(ig))
		} else {
			// expr type not yet covered in code
		}
	}
	public Set<DashDynSymbol> getDynamicSymbols() {
		// look for which unbound vars (fully qualified name + params) in the symbol table are used in this expression
		assert(resolved == true);
		return recurseGetDynamicSymbols(ae, emptySet());
	}
	*/

}