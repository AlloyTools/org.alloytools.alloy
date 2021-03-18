package edu.mit.csail.sdg.ast;

import edu.mit.csail.sdg.alloy4.Pos;

public class DashDoExpr {

    public Pos  pos;
    public Expr expr;

    public DashDoExpr(Pos pos, Expr expr) {
        this.pos = pos;
        this.expr = expr;
    }
}
