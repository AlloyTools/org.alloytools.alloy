package edu.mit.csail.sdg.parser;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.List;

import edu.mit.csail.sdg.ast.DashConcState;
import edu.mit.csail.sdg.ast.DashEvent;
import edu.mit.csail.sdg.ast.DashInvariant;
import edu.mit.csail.sdg.ast.DashState;
import edu.mit.csail.sdg.ast.DashTrans;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;

public class CoreDashGenerator {

    static String coreDashModel = "";
    static int    tabCount      = 0;

    public static void printCoreDash(DashModule module) throws IOException {

        for (DashConcState concState : module.topLevelConcStates.values()) {
            printConcState(concState);
        }

        for (DashTrans trans : module.transitions.values()) {
            printTransition(trans);
        }

        coreDashModel += "\n}";

        BufferedWriter writer = new BufferedWriter(new FileWriter("D:/CoreDashOutput.txt"));
        writer.write(coreDashModel);

        writer.close();

        System.out.println(coreDashModel);
    }

    static void printConcState(DashConcState concState) {
        DashConcState current = concState;

        coreDashModel += ("conc state " + current.name + " {" + '\n');

        for (Decl decl : current.decls) {
            coreDashModel += (decl.get().toString() + ": " + decl.expr.toString() + '\n');
        }

        for (DashEvent event : current.events) {
            coreDashModel += (event.type + " " + event.name + "{}\n");
        }

        if (current.invariant.size() > 0) {
            for (DashInvariant dashExpr : current.invariant) {
                coreDashModel += ("invariant " + dashExpr.name + "{\n");
                coreDashModel += (dashExpr.expr.toString());
                coreDashModel += ("}\n");
            }
        }

        if (current.init.size() > 0) {
            for (DashInvariant dashExpr : current.invariant) {
                coreDashModel += ("init " + dashExpr.name + "{\n");
                coreDashModel += (dashExpr.expr.toString());
                coreDashModel += ("}\n");
            }
        }

        for (DashState state : current.states) {
            printState(state);
        }
        coreDashModel += '\n';

        for (DashConcState innerConcState : current.concStates) {
            printConcState(innerConcState);
            coreDashModel += "}\n";
        }
    }

    static void printState(DashState state) {
        coreDashModel += (tabLine(++tabCount) + "state " + state.name + "{}");

        for (DashState innerState : state.states) {
            printState(innerState);
            coreDashModel += '\n';
        }

        coreDashModel += (tabLine(--tabCount) + '\n');
    }

    static void printTransition(DashTrans transition) {
        coreDashModel += (tabLine(++tabCount) + "trans " + transition.modifiedName + "{" + '\n');

        for (String fromExpr : transition.fromExpr.fromExpr)
            coreDashModel += (tabLine(tabCount) + "from " + fromExpr + '\n');
        if ((transition.onExpr != null))
            coreDashModel += (tabLine(tabCount) + "on " + transition.onExpr.name + '\n');
        if (transition.whenExpr != null)
            printExprList("when", transition.whenExpr.exprList);
        if (transition.doExpr != null)
            printExprList("do", transition.doExpr.exprList);
        for (String gotoExpr : transition.gotoExpr.gotoExpr)
            coreDashModel += (tabLine(tabCount) + "goto " + gotoExpr + '\n');

        coreDashModel += (tabLine(--tabCount) + "}" + '\n');
    }

    static void printExprList(String commandName, List<Expr> exprList) {
        if (exprList.size() > 1) {
            coreDashModel += (tabLine(tabCount) + commandName + " {" + '\n');
            for (Expr expr : exprList)
                coreDashModel += (tabLine(tabCount) + expr.toString() + '\n');
            coreDashModel += (tabLine(tabCount) + "}" + '\n');
        } else {
            coreDashModel += (tabLine(tabCount) + commandName + " " + exprList.get(0) + '\n');
        }
    }

    static String tabLine(int count) {
        String tabs = "";

        for (int i = 0; i < count; i++) {
            tabs += '\t';
        }
        return tabs;
    }
}
