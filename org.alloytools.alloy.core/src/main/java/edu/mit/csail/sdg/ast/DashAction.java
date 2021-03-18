package edu.mit.csail.sdg.ast;

import edu.mit.csail.sdg.alloy4.Pos;

public class DashAction {

    public Pos    pos;
    public String name;
    public Expr   expr;

    public DashAction(Pos pos, String name, Expr expr) {
        this.pos = pos;
        this.name = name;
        this.expr = expr;
    }
}
