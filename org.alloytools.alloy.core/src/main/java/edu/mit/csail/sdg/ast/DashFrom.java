package edu.mit.csail.sdg.ast;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;

public class DashFrom {

    public Pos          pos;
    public List<String> fromExpr = new ArrayList<String>();
    public Boolean      fromAll;

    public DashFrom(Pos pos, List<ExprVar> fromExpr, Boolean fromAll) {
        this.pos = pos;

        if (fromExpr.size() > 0) {
            for (ExprVar var : fromExpr) {
                this.fromExpr.add(var.toString());
            }
        }

        this.fromAll = fromAll;
    }

}
