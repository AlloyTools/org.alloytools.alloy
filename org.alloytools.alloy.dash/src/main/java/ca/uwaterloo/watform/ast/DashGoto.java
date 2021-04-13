package ca.uwaterloo.watform.ast;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.ExprVar;

public class DashGoto {

    public Pos          pos;
    public List<String> gotoExpr = new ArrayList<String>();
    public String       name;

    public DashGoto(Pos pos, List<ExprVar> gotoExpr) {
        this.pos = pos;

        if (gotoExpr.size() > 0) {
            for (ExprVar var : gotoExpr) {
                this.gotoExpr.add(var.toString());
            }
        }
    }

    /*
     * Used when the TransfromCoreDash expands transitions and creates a new
     * DashGoto Object
     */
    public DashGoto(List<String> gotoExpr) {
        this.pos = null;
        this.gotoExpr = gotoExpr;
    }

    public DashGoto(String gotoExpr) {
        this.pos = null;
        this.gotoExpr.add(gotoExpr);
    }
}
