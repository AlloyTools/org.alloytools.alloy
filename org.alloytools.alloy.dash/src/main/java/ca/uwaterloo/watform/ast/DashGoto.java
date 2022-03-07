package ca.uwaterloo.watform.ast;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.ExprVar;

public class DashGoto {

    public Pos          pos;
    public List<String> gotoExpr = new ArrayList<String>();
    public String       name;
    public String       param;
    
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
    public DashGoto(Pos pos, List<String> gotoExpr, String param) {
        this.pos = pos;
        this.gotoExpr = new ArrayList<String>(gotoExpr);
        this.param = param;
    }
    
    /*
     * Used by the Grammer file to create a parameterized Goto expression
     */
   public DashGoto(Pos pos, String gotoExpr, String param) {
       this.pos = pos;
       this.gotoExpr = new ArrayList<String>(Arrays.asList(gotoExpr));
       this.param = param;
       System.out.println("Param: " + param);
   }
    
    public DashGoto(List<String> gotoExpr) {
        this.pos = null;
        this.gotoExpr = new ArrayList<String>(gotoExpr);
    }

    public DashGoto(String gotoExpr) {
        this.pos = null;
        this.gotoExpr.add(gotoExpr);
    }
    
}
