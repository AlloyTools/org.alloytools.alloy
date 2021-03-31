package edu.mit.csail.sdg.parser;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Options;
import edu.mit.csail.sdg.ast.DashAction;
import edu.mit.csail.sdg.ast.DashConcState;
import edu.mit.csail.sdg.ast.DashEvent;
import edu.mit.csail.sdg.ast.DashInit;
import edu.mit.csail.sdg.ast.DashInvariant;
import edu.mit.csail.sdg.ast.DashState;
import edu.mit.csail.sdg.ast.DashTrans;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;

public class CoreDashGenerator {

    static String coreDashModel = "";
    static int    tabCount      = 0;

    public static void printCoreDash(DashModule module) throws IOException {

        coreDashModel = "";

        for (DashConcState concState : module.topLevelConcStates.values()) {
            printConcState(concState);
        }

        for (DashTrans trans : module.transitions.values()) {
            printTransition(trans);
        }

        coreDashModel += "\n}";

        BufferedWriter writer = new BufferedWriter(new FileWriter(Options.outputDir + ".dsh"));
        writer.write(coreDashModel);

        writer.close();
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

        coreDashModel += '\n';

        if (current.invariant.size() > 0) {
            for (DashInvariant dashExpr : current.invariant) {
                coreDashModel += ("invariant " + dashExpr.name + "{\n");
                coreDashModel += (dashExpr.expr.toString());
                coreDashModel += ("}\n\n");
            }
            coreDashModel += '\n';
        }

        if (current.init.size() > 0) {
            for (DashInit init : current.init) {
                coreDashModel += ("init generated_name" + "{\n");
                for (Expr expr : init.exprList) {
                    coreDashModel += (expr.toString() + '\n');
                }
                coreDashModel += ("}\n\n");
            }
            coreDashModel += '\n';
        }


        if (current.action.size() > 0) {
            for (DashAction action : current.action) {
                coreDashModel += ("action " + action.name + "{\n");
                for (Expr expr : action.exprList) {
                    coreDashModel += (expr.toString() + '\n');
                }
                coreDashModel += ("}\n\n");
            }
            coreDashModel += '\n';
        }

        for (DashState state : current.states) {
            printState(state);
            coreDashModel += '\n';
        }


        for (DashConcState innerConcState : current.concStates) {
            printConcState(innerConcState);
            coreDashModel += "}\n";
        }
    }

    static void printState(DashState state) {
        coreDashModel += (tabLine(tabCount) + "state " + state.name + "{}");

        if (state.states.size() > 0) {
            coreDashModel += "{\n";
            for (DashState innerState : state.states) {
                printState(innerState);
            }
            coreDashModel += "}\n";
        }

        coreDashModel += (tabLine(tabCount) + '\n');
    }

    static void printTransition(DashTrans transition) {
        coreDashModel += (tabLine(++tabCount) + "trans " + transition.modifiedName + "{" + '\n');

        if (transition.fromExpr.fromExpr.size() > 0)
            coreDashModel += (tabLine(tabCount) + "from " + transition.fromExpr.fromExpr.get(0) + '\n');
        if (transition.onExpr != null && transition.onExpr.name != null)
            coreDashModel += (tabLine(tabCount) + "on " + transition.onExpr.name + '\n');
        if (transition.whenExpr != null)
            printExprList("when", transition.whenExpr.exprList);
        if (transition.doExpr != null)
            printExprList("do", transition.doExpr.exprList);
        if (transition.gotoExpr.gotoExpr.size() > 0)
            coreDashModel += (tabLine(tabCount) + "goto " + transition.gotoExpr.gotoExpr.get(0) + '\n');

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
