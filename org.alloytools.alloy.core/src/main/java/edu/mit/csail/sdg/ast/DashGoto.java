package edu.mit.csail.sdg.ast;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;

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
}
