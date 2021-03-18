package edu.mit.csail.sdg.ast;

import edu.mit.csail.sdg.alloy4.Pos;

public class DashInvariant {

    public Pos    pos;
    public String name;
    public Expr   expr;

    public DashInvariant(Pos pos, String name, Expr expr) {
        this.pos = pos;
        this.name = name;
        this.expr = expr;
    }
}
