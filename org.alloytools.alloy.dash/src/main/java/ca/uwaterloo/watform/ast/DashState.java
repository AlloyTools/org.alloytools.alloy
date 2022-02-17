package ca.uwaterloo.watform.ast;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.Pos;

public class DashState {

    public Pos             pos;
    public String          name         = "";
    public String          modifiedName = "";
    public Object          parent       = null;

    public List<DashState> states       = new ArrayList<DashState>();
    public List<DashEnter> enter       = new ArrayList<DashEnter>();
    public List<DashExit>  exit       = new ArrayList<DashExit>();
    public List<DashTrans> transitions  = new ArrayList<DashTrans>();
    public List<DashTrans> modifiedTransitions  = new ArrayList<DashTrans>(); 
    public Boolean         isDefault;  //Specifies whether this state is a default state


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
                if (item instanceof DashEnter) 
                    this.enter.add((DashEnter) item);
                if (item instanceof DashExit) 
                    this.exit.add((DashExit) item);
                if (item instanceof DashEvent)
                    throw new ErrorSyntax(((DashEvent) item).pos, "Cannot declare an event inside a state");
                if (item instanceof DashExpr)
                    throw new ErrorSyntax(((DashExpr) item).pos, "Illegal declaration inside a state");
            }
        }

        this.isDefault = isDefault;
    }
    
    public DashState(DashState state) {
        state.pos = this.pos; //This specifies the position of the state in the model (line and column information)     
        state.name = this.name;
        state.modifiedName = this.modifiedName;
        state.parent = this.parent;            
        state.states = this.states;
        state.enter = this.enter;
        state.exit = this.exit;
        state.transitions = this.transitions;
        state.modifiedTransitions = this.modifiedTransitions;
        state.isDefault = this.isDefault;
    }

}
