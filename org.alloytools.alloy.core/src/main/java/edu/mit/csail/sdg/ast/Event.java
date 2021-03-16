package edu.mit.csail.sdg.ast;

import edu.mit.csail.sdg.alloy4.Pos;

public class Event {

    public Pos    pos;
    public String name = "";
    public String type = "";
    public Decl   decl;

    public Event(Pos pos, String name, String type) {
        this.pos = pos;
        this.name = name;
        this.type = type;
    }

    public Event(Pos pos, Decl decl, String type) {
        this.pos = pos;
        this.decl = decl;
        this.type = type;
    }
}
