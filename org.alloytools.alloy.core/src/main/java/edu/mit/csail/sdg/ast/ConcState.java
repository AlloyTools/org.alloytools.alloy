package edu.mit.csail.sdg.ast;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;

/* This class is responsible for holding information regarding each concurrent state
 * declared within a DASH model */
public class ConcState {

    public Pos                 pos;
    public String              name         = "";
    public String              modifiedName = "";

    public List<ConcState>     concStates   = new ArrayList<ConcState>();
    public List<State>         states       = new ArrayList<State>();
    public List<Trans>         transitions  = new ArrayList<Trans>();
    public List<Event>         events       = new ArrayList<Event>();
    public List<Decl>          decls        = new ArrayList<Decl>();
    public List<DashInit>      init         = new ArrayList<DashInit>();
    public List<DashInvariant> invariant    = new ArrayList<DashInvariant>();
    public List<DashAction>    action       = new ArrayList<DashAction>();
    public List<DashCondition> condition    = new ArrayList<DashCondition>();

    /*
     * This constructor is called by DashParser.java when it completes parsing a
     * concurrent state. concStateItems are the list of items that are inside the
     * parsed conc state.
     */
    public ConcState(Pos pos, String name, List<Object> concStateItems) {
        this.pos = pos;
        this.name = name;

        //Iterate through each item in the conc state and add each item to
        //a respective list (A state item will be added to the list of states, etc)
        for (Object item : concStateItems) {
            if (item instanceof ConcState)
                concStates.add((ConcState) item);
            if (item instanceof State)
                states.add((State) item);
            if (item instanceof Trans)
                transitions.add((Trans) item);
            if (item instanceof Decl)
                decls.add((Decl) item);
            if (item instanceof Event)
                events.add((Event) item);
            if (item instanceof DashInit)
                init.add((DashInit) item);
            if (item instanceof DashInvariant)
                invariant.add((DashInvariant) item);
            if (item instanceof DashAction)
                action.add((DashAction) item);
            if (item instanceof DashCondition)
                condition.add((DashCondition) item);
        }

    }
}
