package ca.uwaterloo.watform.ast;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

public class DashInvariant {

    public Pos           pos;
    public String        name;
    public Expr          expr;
    public DashConcState parent;
    public List<Expr>    exprList = new ArrayList<Expr>();

    public DashInvariant(Pos pos, String name, Expr expr) {
        this.pos = pos;
        this.name = name;
        this.expr = expr;
    }
}
