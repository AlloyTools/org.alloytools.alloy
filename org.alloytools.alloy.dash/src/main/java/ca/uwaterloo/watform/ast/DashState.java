package ca.uwaterloo.watform.ast;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.Pos;

public class DashState {

    public Pos             pos;
    public String          name            = "";
    public String          modifiedName    = "";
    public DashConcState   parentConcState = null; 
    public Object          parent          = null;

    public List<DashState> states          = new ArrayList<DashState>();
    public List<DashTrans> transitions     = new ArrayList<DashTrans>();
    public Boolean         isDefault;      //Specifies whether this state is a default state


    /*
     * This constructor is called by DashParser.java when it completes parsing a
     * state. items are the list of items that are inside the parsed state.
     */
    public DashState(Pos pos, String label, List<Object> stateItems, Boolean isDefault) {
        this.pos = pos; //This specifies the position of the state in the model (line and column information)
        this.name = label;
        this.states = new ArrayList<DashState>();
        this.transitions = new ArrayList<DashTrans>();

        if (stateItems != null) {
            for (Object item : stateItems) {
                if (item instanceof DashState)
                    this.states.add((DashState) item);
                if (item instanceof DashTrans)
                    this.transitions.add((DashTrans) item);
                if (item instanceof DashEvent)
                    throw new ErrorSyntax(((DashEvent) item).pos, "Cannot declare an event inside a state");
                if (item instanceof DashExpr)
                    throw new ErrorSyntax(((DashExpr) item).pos, "Illegal declaration inside a state");
            }
        }

        this.isDefault = isDefault;
    }

}