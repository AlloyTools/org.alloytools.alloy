package edu.mit.csail.sdg.ast;

import edu.mit.csail.sdg.alloy4.Pos;

public class DashEnter {

    public Expr expr;
    public Pos  pos;

    public DashEnter(Pos pos, Expr expr) {
        this.expr = expr;
        this.pos = pos;
    }

}
