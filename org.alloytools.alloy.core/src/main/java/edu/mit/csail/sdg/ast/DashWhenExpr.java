package edu.mit.csail.sdg.ast;

import edu.mit.csail.sdg.alloy4.Pos;

public class DashWhenExpr {

    public Pos  pos;
    public Expr expr;

    public DashWhenExpr(Pos pos, Expr expr) {
        this.pos = pos;
        this.expr = expr;
    }
}
