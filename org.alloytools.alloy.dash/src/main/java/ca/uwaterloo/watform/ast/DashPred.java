package ca.uwaterloo.watform.ast;



import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.DashStrings;

public class DashPred extends Dash {

    public Expr exp;
    public String name; // has no meaning
 
    public DashPred(Pos p, String n, Expr i) {
        assert(n != null && i != null);
        this.pos = pos;
        this.name = n;
        this.exp = i;
    }
    public String toString() {
        String s = new String();
        s += DashStrings.predName +" "; 
        if (name != null) s += name;
        s += " {\n";
        s += exp.toString() + "\n";
        return s + "}\n";
    }
    public Expr getExp() {
        return exp;
    }
    public String getName() {
        return name;
    }
}