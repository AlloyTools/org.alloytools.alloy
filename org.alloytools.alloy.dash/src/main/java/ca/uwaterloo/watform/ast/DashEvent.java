package ca.uwaterloo.watform.ast;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Decl;

public class DashEvent {

    public Pos    pos;
    public String parentName = "";
    public String name       = "";
    public String modifiedName       = "";
    public String type       = "";
    public Decl   decl;

    public DashEvent(Pos pos, String name, String type) {
        this.pos = pos;
        this.name = name;
        this.type = type;
    }

    public DashEvent(Pos pos, Decl decl, String type) {
        this.pos = pos;
        this.decl = decl;
        this.type = type;
    }
}
