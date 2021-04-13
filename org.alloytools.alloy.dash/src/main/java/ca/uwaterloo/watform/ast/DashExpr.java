package ca.uwaterloo.watform.ast;

import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprVar;

/* Separate this file into different files */
/* This stores about init, action, condition, do, when, etc. declarations inside a Dash Model  */
public final class DashExpr {

    public String        name          = null;
    public List<ExprVar> templateParam = null;
    public Expr          expr          = null;
    public String        type          = null;
    public Pos           pos           = null;
    public List<Expr>    exprs;
    public List<ExprVar> names;

    /* Used for instantiating a transition template */
    public DashExpr(Pos pos, String templateName, List<ExprVar> templateParam, String type) {
        this.pos = pos;
        this.name = templateName;
        this.templateParam = templateParam;
        this.type = type;
        this.expr = null;
        this.exprs = null;
    }

    public DashExpr(Pos pos, Expr v, String type) {
        this.pos = pos;
        this.name = null;
        this.expr = v;
        this.type = type;
        this.exprs = null;
        this.templateParam = null;
    }

    public DashExpr(Pos pos, String name, String type) {
        this.pos = pos;
        this.name = name;
        this.expr = null;
        this.type = type;
        this.exprs = null;
        this.templateParam = null;
    }

    public DashExpr(Pos pos, String name, Expr v, String type) {
        this.pos = pos;
        this.name = name;
        this.expr = v;
        this.type = type;
        this.exprs = null;
        this.templateParam = null;
    }

    /* Used for instantiating For commands in a transition */
    public DashExpr(Pos pos, List<ExprVar> names, String type, String n) {
        this.pos = pos;
        if (names != null)
            this.names = names;
        this.expr = null;
        this.type = type;
        this.exprs = null;
        this.templateParam = null;
    }

    public DashExpr(Pos pos, List<Expr> exprs, String type) {
        this.pos = pos;
        this.name = null;
        this.expr = null;
        this.type = type;
        this.exprs = exprs;
        this.templateParam = null;
    }
}
