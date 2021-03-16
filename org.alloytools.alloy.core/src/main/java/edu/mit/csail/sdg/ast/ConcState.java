package edu.mit.csail.sdg.ast;

import java.util.ArrayList;
import java.util.List;

/* This class is responsible for holding information regarding each concurrent state
 * declared within a DASH model */
public class ConcState {

    public String          name;
    public String          modifiedName = "";

    public List<ConcState> concStates   = new ArrayList<ConcState>();
    public List<State>     states       = new ArrayList<State>();
    public List<Trans>     transitions  = new ArrayList<Trans>();
    public List<Event>     events       = new ArrayList<Event>();
    public List<Decl>      decls        = new ArrayList<Decl>();
    public List<DashExpr>  init         = new ArrayList<DashExpr>();
    public List<DashExpr>  invariant    = new ArrayList<DashExpr>();
    public List<DashExpr>  action       = new ArrayList<DashExpr>();
    public List<DashExpr>  condition    = new ArrayList<DashExpr>();

    /*
     * This constructor is called by DashParser.java when it completes parsing a
     * concurrent state. concStateItems are the list of items that are inside the
     * parsed conc state.
     */
    public ConcState(String name, List<Object> concStateItems) {
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
            if (item instanceof DashExpr) {
                if (((DashExpr) item).type.equals("init"))
                    init.add((DashExpr) item);
            }
            if (item instanceof DashExpr) {
                if (((DashExpr) item).type.equals("invariant"))
                    invariant.add((DashExpr) item);
            }
            if (item instanceof DashExpr) {
                if (((DashExpr) item).type.equals("action"))
                    action.add((DashExpr) item);
            }
            if (item instanceof DashExpr) {
                if (((DashExpr) item).type.equals("condition"))
                    condition.add((DashExpr) item);
            }

        }

    }
}
