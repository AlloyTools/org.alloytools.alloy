package ca.uwaterloo.watform.ast;

import edu.mit.csail.sdg.alloy4.Pos;

public class DashOn {

    public Pos    pos;
    public String name;
    public Boolean isInternal = false;

    public DashOn(Pos pos, String name, Boolean isInternal) {
        this.pos = pos;
        this.name = name;
        this.isInternal = isInternal;
    }
}
