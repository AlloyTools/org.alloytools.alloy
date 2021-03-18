package edu.mit.csail.sdg.parser;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import edu.mit.csail.sdg.ast.ConcState;
import edu.mit.csail.sdg.ast.DashAction;
import edu.mit.csail.sdg.ast.DashCondition;
import edu.mit.csail.sdg.ast.DashInit;
import edu.mit.csail.sdg.ast.DashInvariant;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Event;
import edu.mit.csail.sdg.ast.State;
import edu.mit.csail.sdg.ast.Trans;

public class CoreDashGenerator {

    private Map<String,ConcState> concStates     = new LinkedHashMap<String,ConcState>();

    private List<String>          concStateNames = new ArrayList<String>();

    private Map<String,State>     states         = new LinkedHashMap<String,State>();

    private Map<String,Trans>     transitions    = new LinkedHashMap<String,Trans>();

    public String                 coreDashModel  = "";

    public int                    tabCount       = 0;

    public CoreDashGenerator(Map<String,ConcState> concStates, List<String> concStateNames, Map<String,State> states, Map<String,Trans> transitions) {
        this.concStates = concStates;
        this.concStateNames = concStateNames;
        this.states = states;
        this.transitions = transitions;
    }

    public void printCoreDash() {

        for (String name : concStateNames) {
            printConcState(name);
        }

        System.out.println(coreDashModel);
    }

    void printConcState(String name) {
        ConcState current = concStates.get(name);

        coreDashModel += ("conc state " + name + " {" + '\n');

        for (Decl decl : current.decls) {
            coreDashModel += (decl.get().toString() + ": " + decl.expr.toString() + '\n');
        }
        coreDashModel += '\n';

        for (Event event : current.events) {
            coreDashModel += (event.type + " " + event.name + '\n');
        }
        coreDashModel += '\n';

        if (current.invariant.size() > 0) {
            for (DashInvariant dashExpr : current.invariant) {
                coreDashModel += ("invariant " + dashExpr.name + "{\n");
                coreDashModel += (dashExpr.expr.toString());
                coreDashModel += ("}\n");
            }
        }

        if (current.init.size() > 0) {
            coreDashModel += ("init {\n");
            for (DashInit dashExpr : current.init)
                coreDashModel += (dashExpr.expr.toString());
            coreDashModel += ("}\n");
        }

        if (current.action.size() > 0) {
            coreDashModel += ("action {\n");
            for (DashAction dashExpr : current.action)
                coreDashModel += (dashExpr.expr.toString());
            coreDashModel += ("}\n");
        }

        if (current.condition.size() > 0) {
            coreDashModel += ("v {\n");
            for (DashCondition dashExpr : current.condition)
                coreDashModel += (dashExpr.expr.toString());
            coreDashModel += ("}\n");
        }

        for (State state : current.states) {
            printState(state);
            coreDashModel += '\n';
        }

        for (Trans trans : current.transitions) {
            printTransition(trans);
            coreDashModel += '\n';
        }
    }

    void printState(State state) {
        coreDashModel += (tabLine(++tabCount) + "state " + state.name + "{" + '\n');

        for (State innerState : state.states) {
            printState(innerState);
            coreDashModel += '\n';
        }

        for (Trans transition : state.transitions) {
            printTransition(transition);
            coreDashModel += '\n';
        }
        coreDashModel += (tabLine(--tabCount) + "}" + '\n');
    }

    void printTransition(Trans transition) {
        coreDashModel += (tabLine(++tabCount) + "trans " + transition.name + "{" + '\n');

        for (String fromExpr : transition.fromExpr.fromExpr)
            coreDashModel += (tabLine(tabCount) + "from " + fromExpr + '\n');
        if ((transition.onExpr != null))
            coreDashModel += (tabLine(tabCount) + "on " + transition.onExpr + '\n');
        if (transition.whenExpr != null)
            coreDashModel += (tabLine(tabCount) + "when " + transition.whenExpr.toString() + '\n');
        if (transition.doExpr != null)
            coreDashModel += (tabLine(tabCount) + "do " + transition.doExpr.toString() + '\n');
        for (String gotoExpr : transition.gotoExpr.gotoExpr)
            coreDashModel += (tabLine(tabCount) + "goto " + gotoExpr + '\n');


        coreDashModel += (tabLine(--tabCount) + "}" + '\n');
    }

    String tabLine(int count) {
        String tabs = "";

        for (int i = 0; i < count; i++) {
            tabs += '\t';
        }

        return tabs;
    }
}
