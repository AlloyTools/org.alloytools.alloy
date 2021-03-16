package edu.mit.csail.sdg.ast;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.Pos;

public class State {

    public Pos         pos;
    public String      name         = "";
    public String      modifiedName = "";
    public String      parentConc   = "";
    public State       parentState  = null;

    public List<State> states       = new ArrayList<State>();
    public List<Trans> transitions  = new ArrayList<Trans>();
    public Boolean     isDefault;  //Specifies whether this state is a default state


    /*
     * This constructor is called by DashParser.java when it completes parsing a
     * state. items are the list of items that are inside the parsed state.
     */
    public State(Pos pos, String label, List<Object> stateItems, Boolean isDefault) {
        this.pos = pos; //This specifies the position of the state in the model (line and column information)
        this.name = label;
        this.states = new ArrayList<State>();
        this.transitions = new ArrayList<Trans>();

        if (stateItems != null) {
            for (Object item : stateItems) {
                if (item instanceof State)
                    this.states.add((State) item);
                if (item instanceof Trans)
                    this.transitions.add((Trans) item);
                if (item instanceof Event)
                    throw new ErrorSyntax(((Event) item).pos, "Cannot declare an event inside a state");
                if (item instanceof DashExpr)
                    throw new ErrorSyntax(((DashExpr) item).pos, "Illegal declaration inside a state");
            }
        }

        this.isDefault = isDefault;
    }

}
