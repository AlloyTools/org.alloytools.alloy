package ca.uwaterloo.watform.ast;

import edu.mit.csail.sdg.alloy4.Pos;

public class DashOn {

    public Pos    	     pos;
    public DashConcState parent;
    public String 		 name;
    public Boolean 		 isInternal = false;

    public DashOn(Pos pos, String name, Boolean isInternal) {
        this.pos = pos;
        this.name = name;
        this.isInternal = isInternal;
    }
    
    public DashOn(DashOn on) {
    	this.pos = on.pos;
    	this.parent = on.parent;
    	this.name = on.name;
    	this.isInternal = on.isInternal;
    }
}
