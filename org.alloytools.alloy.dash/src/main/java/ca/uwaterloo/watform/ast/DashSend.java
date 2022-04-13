package ca.uwaterloo.watform.ast;

import edu.mit.csail.sdg.alloy4.Pos;

public class DashSend {

    public Pos           		 pos;
    public DashConcState parent;
    public String 		 name;
    public String 	     param;

    public DashSend(Pos pos, String name) {
        this.pos = pos;
        this.name = name;
    }
    
    public DashSend(Pos pos, String name, String param) {
        this.pos = pos;
        this.name = name;
        this.param = param;
    }
    
    public DashSend (DashSend send) {
    	this.pos = send.pos == null ? null : send.pos;
    	this.parent = send.parent == null ? null : send.parent;
    	this.param = send.param == null ? null : send.param;
    	this.name = send.name;
    }
}
