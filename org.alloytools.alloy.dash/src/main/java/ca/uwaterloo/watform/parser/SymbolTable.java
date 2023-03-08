package ca.uwaterloo.watform.parser;

import java.util.ArrayList;
import java.util.HashMap;

import edu.mit.csail.sdg.ast.Expr;
import ca.uwaterloo.watform.core.DashStrings;

public class SymbolTable {

	private HashMap<String,DynSymbol> table;
	private int NOTBUFFER = -1;

	public class DynSymbol  {

		private int index; // used for buffers
		// tmp
		private String typ;
		// private DashExpr exp; // type expression
		private DashStrings.IntEnvKind kind;

		// for variables
		public DynSymbol(Expr e, DashStrings.IntEnvKind k) {
			this.index = NOTBUFFER;
			// tmp
			this.typ = null;
			this.kind = k;

		}
		// for buffers
		public DynSymbol(int idx, DashStrings.IntEnvKind k, String elements) {
			this.index = idx;
			// temporary
			this.typ = elements;
			// this.typ = DashExpr(createArrow(DashStrings.bufferIndexName+idx, elements));
			this.kind = k;

		}		
	}
	public SymbolTable() {
		this.table = new HashMap<String,DynSymbol>();
	}
	/*
	public void addDeclaredVar(String n, List<String> prs, Expr e, EventVarKind k) {
		if (!table.keys().contains(n)) {
			table.put(n,DynVar(i,prs,e,k))
		} else {
			if (table.get(n).declared) // err declared twice
			else table.get(n) = DynVar(i,prs,e,k);
		}
	}
	*/
	public void addDeclaredBuffer(String n, int idx,  DashStrings.IntEnvKind k, String elements) {
		if (!table.keySet().contains(n)) {
			table.put(n,new DynSymbol(idx,k,elements));
		} else {
			if (table.get(n) != null) { ; } // err declared twice 
			else table.put(n, new DynSymbol(idx,k,elements));
		}
	}
	/*
	public void addUsedVar(String n) {
		if ( !(table.keys().contains(n))) table.put(n,null);
	}
	public void addUsedBuffer(String n) {
		if ( !(table.keys().contains(n))) table.put(n,null);
	}
	public void resolveAll() {
		// check for any vars used but not declared
		for (e:table.keys()) {
			if (table.get(e) == null) {
				// err used but not declared
			}
		}
	}
	*/
	/*
		creates the fully qualified name
		uses snapshot or not for Electrum
		joins with params
	*/
	/*
	public AlloyExpr createAlloyExprVar(boolean primed) {
		String n = pathHere+"/"+name;
		if (DashOptions.isElectrum() && primed) {
			n = DashStrings.prime(n) ;
		}
		ExprVar e = createVar(n)
		if (!DashOptions.isElectrum()) {
			if (!primed) {		
				s = DashStrings.sCur;
				e = AlloyExprHelper.createExprJoin(s,e)
			} else {
				s = DashStrings.sNext;
				e = AlloyExprHelper.createExprJoin(s,e)
			} 		
		}
		// turn all the params into vars
		return AlloyExprHelper.createExprJoin (p0.p1.p2.e)		
	}

	// used for snapshot declarations
	// probably will have to return exp and then convert
	public Expr createAlloyTyp(symboltable) {
		// does it have to convert anything??
		return typ.convertToAlloy(symboltable)
	}
	*/
}
