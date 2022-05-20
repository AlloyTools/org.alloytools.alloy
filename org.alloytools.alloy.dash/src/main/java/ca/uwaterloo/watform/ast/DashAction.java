package ca.uwaterloo.watform.ast;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

import org.apache.velocity.VelocityContext;
import org.apache.velocity.Template;
import org.apache.velocity.app.VelocityEngine;

public class DashAction {

    public Pos           pos;
    public String        name;
    public DashConcState parent;
    public Expr          expr;
    public List<Expr>    exprList = new ArrayList<Expr>();

    public DashAction(Pos pos, String name, Expr expr) {
        this.pos = pos;
        this.name = name;
        this.expr = expr;
    }
}
