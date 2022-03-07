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
    public DashConcState parent = null;
    public boolean isParameterized = false;

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
    
    public DashEvent(Pos pos, Decl decl, String type, boolean isParameterized) {
        this.pos = pos;
        this.decl = decl;
        this.type = type;
        this.isParameterized = isParameterized;
    }
    
    public DashEvent(DashEvent event) {
        this.pos = event.pos;
        this.parentName = event.parentName;
        this.name = event.name;
        this.modifiedName = event.modifiedName;
        this.type = event.type;
        this.decl = event.decl;
        this.parent = event.parent;
        this.isParameterized = event.isParameterized;
    }
}
