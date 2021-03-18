package edu.mit.csail.sdg.parser;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import edu.mit.csail.sdg.ast.DashAction;
import edu.mit.csail.sdg.ast.DashConcState;
import edu.mit.csail.sdg.ast.DashCondition;
import edu.mit.csail.sdg.ast.DashInit;
import edu.mit.csail.sdg.ast.DashInvariant;
import edu.mit.csail.sdg.ast.DashState;
import edu.mit.csail.sdg.ast.DashTrans;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Event;

public class CoreDashGenerator {

    private Map<String,DashConcState> concStates     = new LinkedHashMap<String,DashConcState>();

    private List<String>              concStateNames = new ArrayList<String>();

    private Map<String,DashState>     states         = new LinkedHashMap<String,DashState>();

    private Map<String,DashTrans>     transitions    = new LinkedHashMap<String,DashTrans>();

    public String                     coreDashModel  = "";

    public int                        tabCount       = 0;

    public CoreDashGenerator(Map<String,DashConcState> concStates, List<String> concStateNames, Map<String,DashState> states, Map<String,DashTrans> transitions) {
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
        DashConcState current = concStates.get(name);

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

        for (DashState state : current.states) {
            printState(state);
            coreDashModel += '\n';
        }

        for (DashTrans trans : current.transitions) {
            printTransition(trans);
            coreDashModel += '\n';
        }
    }

    void printState(DashState state) {
        coreDashModel += (tabLine(++tabCount) + "state " + state.name + "{" + '\n');

        for (DashState innerState : state.states) {
            printState(innerState);
            coreDashModel += '\n';
        }

        for (DashTrans transition : state.transitions) {
            printTransition(transition);
            coreDashModel += '\n';
        }
        coreDashModel += (tabLine(--tabCount) + "}" + '\n');
    }

    void printTransition(DashTrans transition) {
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
