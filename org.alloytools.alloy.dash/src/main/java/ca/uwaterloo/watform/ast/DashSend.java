package ca.uwaterloo.watform.ast;

import edu.mit.csail.sdg.alloy4.Pos;

public class DashSend {

    Pos           pos;
    public String name;

    public DashSend(Pos pos, String name) {
        this.pos = pos;
        this.name = name;
    }
}
