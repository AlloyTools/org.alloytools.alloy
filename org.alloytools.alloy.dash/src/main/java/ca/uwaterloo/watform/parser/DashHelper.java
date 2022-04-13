package ca.uwaterloo.watform.parser;

import java.util.ArrayList;
import java.util.List;

import ca.uwaterloo.watform.ast.DashConcState;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;

public class DashHelper {

	public static String toLowerCase(String string) {
		return Character.toLowerCase(string.charAt(0)) + string.substring(1);
	}
	
	public static String toUpperCase(String string) {
		return Character.toUpperCase(string.charAt(0)) + string.substring(1);
	}
	
	public static Expr parameterize(String string) {
		return ExprBinary.Op.JOIN.make(null, null, ExprVar.make(null, "p"), ExprVar.make(null, DashHelper.toLowerCase(string)));
	}
	
	/*
	 * If a Snapshot variable (assume a variable: var) originates from a Parameterized Concurrent State (assume with a parameter called p), then we create the following:
	 * var: p -> expr
	 */
	public static Expr createParameterizedSnapshotVar(String var, Expr expr, DashModule module) {
		DashConcState concState = module.variable2ConcState.get(var);
		Expr parameterizedExpr = null;
		if (expr instanceof ExprUnary) {
			ExprUnary exprUnary = (ExprUnary) expr;		
			if (exprUnary.op == ExprUnary.Op.LONEOF)
				parameterizedExpr = ExprBinary.Op.ANY_ARROW_LONE.make(null, null, ExprVar.make(null, concState.param), exprUnary.sub);
			if (exprUnary.op == ExprUnary.Op.ONEOF)
				parameterizedExpr = ExprBinary.Op.ANY_ARROW_ONE.make(null, null, ExprVar.make(null, concState.param), exprUnary.sub);
			if (exprUnary.op == ExprUnary.Op.SOMEOF)
				parameterizedExpr = ExprBinary.Op.ANY_ARROW_SOME.make(null, null, ExprVar.make(null, concState.param), exprUnary.sub);
			if (exprUnary.op == ExprUnary.Op.SETOF)
				parameterizedExpr = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, concState.param), exprUnary.sub);
		} 
		if (expr instanceof ExprVar) {
			parameterizedExpr = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, concState.param), expr);
		}
		if (expr instanceof ExprBinary) {
			parameterizedExpr = ExprBinary.Op.ARROW.make(null, null, ExprVar.make(null, concState.param), expr);
		}
		return concState.isParameterized ? parameterizedExpr : expr;
	}
	
	public static Expr quantify(String quantifier, String sig, Expr expr) {
        List<Decl> decls = new ArrayList<Decl>();
        List<ExprVar> a = new ArrayList<ExprVar>();
        Expr sigExpr =  ExprVar.make(null, sig);
        a.add(ExprVar.make(null, quantifier));
        decls.add(new Decl(null, null, null, null, a, mult(sigExpr)));
        return ExprQt.Op.ALL.make(null, null, decls, expr);
	}
	
    /*
     * Taken from the Dash.cup file. It is used for handling difficult parsing
     * ambiguities with Alloy expressions
     */
    private static Expr mult(Expr x) throws Err {
        if (x instanceof ExprUnary) {
            ExprUnary y = (ExprUnary) x;
            if (y.op == ExprUnary.Op.SOME)
                return ExprUnary.Op.SOMEOF.make(y.pos, y.sub);
            if (y.op == ExprUnary.Op.LONE)
                return ExprUnary.Op.LONEOF.make(y.pos, y.sub);
            if (y.op == ExprUnary.Op.ONE)
                return ExprUnary.Op.ONEOF.make(y.pos, y.sub);
        }
        return x;
    }

}
