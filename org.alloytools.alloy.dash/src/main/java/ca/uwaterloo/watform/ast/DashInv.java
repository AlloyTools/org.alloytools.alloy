package ca.uwaterloo.watform.ast;



import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.DashStrings;

public class DashInv extends Dash {

    public Expr inv;
    public String name; // has no meaning
    public DashInv(Pos pos, Expr inv) {
        this.pos = pos;
        this.name = null;
        this.inv = inv;
    }
    public DashInv(Pos p, String n, Expr i) {
        assert(n != null && i != null);
        this.pos = pos;
        this.name = n;
        this.inv = i;
    }
    public String toString() {
        String s = new String();
        s += DashStrings.invariantName +" "; 
        if (name != null) s += name;
        s += " {\n";
        s += inv.toString() + "\n";
        return s + "}\n";
    }
    public Expr getInv() {
        return inv;
    }
}