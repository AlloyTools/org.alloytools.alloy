package ca.uwaterloo.watform.ast;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.ExprVar;

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

    public DashFrom(List<String> fromExpr, Boolean fromAll) {
        this.pos = null;
        this.fromExpr = fromExpr;
        this.fromAll = fromAll;
    }

    public DashFrom(String fromExpr, Boolean fromAll) {
        this.pos = null;
        this.fromExpr.add(fromExpr);
        this.fromAll = fromAll;
    }

}
