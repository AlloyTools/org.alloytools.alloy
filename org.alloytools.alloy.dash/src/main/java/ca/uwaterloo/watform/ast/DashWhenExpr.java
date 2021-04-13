package ca.uwaterloo.watform.ast;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

public class DashWhenExpr {

    public Pos        pos;
    public Expr       expr;
    public List<Expr> exprList = new ArrayList<Expr>();

    public DashWhenExpr(Pos pos, Expr expr) {
        this.pos = pos;
        this.expr = expr;
    }
}
