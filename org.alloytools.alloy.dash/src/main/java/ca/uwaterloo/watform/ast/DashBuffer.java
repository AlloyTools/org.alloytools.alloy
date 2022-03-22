package ca.uwaterloo.watform.ast;

import edu.mit.csail.sdg.alloy4.Pos;

public class DashBuffer {

    public Pos  pos;
    public String name;
    public String param;
    public String modifiedName;
    public DashConcState parent;

    public DashBuffer(Pos pos, String name, String param) {
        this.pos = pos;
        this.name = name;
        this.param = param;
    }
}
