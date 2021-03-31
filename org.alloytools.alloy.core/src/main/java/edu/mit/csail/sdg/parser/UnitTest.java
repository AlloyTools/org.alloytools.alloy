package edu.mit.csail.sdg.parser;


import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.ast.DashTrans;

public class UnitTest {

    static List<String> expectedStateNames = Arrays.asList("topStateA", "topStateB");

    //Parser Unit Tests
    public static void testStates() {

        String dashModel = "conc state concState { default state topStateA { default state innerState{}} state topStateB{}}";

        DashModule module = CompUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);

        module.isUnitTest = true;

        if (!expectedStateNames.equals(DashValidation.stateNames.get("concState")))
            throw new ErrorSyntax("Every state has not been stored in the IDS");
        if (!module.states.get("concState_topStateA").states.get(0).name.equals("innerState"))
            throw new ErrorSyntax("Child state has not been stored in the IDS");

        DashValidation.clearContainers();
    }

    public static void testConcStates() {

        String dashModel = "conc state topConcStateA { conc state innerConcState{  default state A {} } } conc state topConcStateB { default state B{} }";

        DashModule module = CompUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);

        module.isUnitTest = true;

        if (!(module.concStates.get("topConcStateA").name.equals("topConcStateA")))
            throw new ErrorSyntax("Top level concurrent state not stored in the IDS");
        if (!(module.concStates.get("topConcStateA").concStates.get(0).name.equals("innerConcState")))
            throw new ErrorSyntax("Child concurrent state not stored in the IDS");
        if (!(module.states.get("topConcStateA_innerConcState_A").name.equals("A")))
            throw new ErrorSyntax("Inner OR state not stored in the IDS");
        if (!(module.concStates.get("topConcStateB").name.equals("topConcStateB")))
            throw new ErrorSyntax("Top level concurrent state not stored in the IDS");

        DashValidation.clearContainers();
    }

    public static void testTransitions() {

        String dashModel = "conc state topConcStateA { event A{} trans A {on A goto B} default state B {trans B {on A}} }";

        DashModule module = CompUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);

        module.isUnitTest = true;

        if (!(module.transitions.get("topConcStateA_A").name.equals("A")))
            throw new ErrorSyntax("Transition not stored in the IDS");
        if (!(module.transitions.get("topConcStateA_B_B").name.equals("B")))
            throw new ErrorSyntax("Transition not stored in the IDS");
        System.out.println("GotExpr: " + module.transitions.get("topConcStateA_A").gotoExpr.gotoExpr.get(0));
        if (!(module.transitions.get("topConcStateA_A").gotoExpr.gotoExpr.get(0).equals("topConcStateA/B")))
            throw new ErrorSyntax("Transition goto not stored in the IDS");
        System.out.println("OnExpr: " + module.transitions.get("topConcStateA_B_B").onExpr.name);
        if (!(module.transitions.get("topConcStateA_B_B").onExpr.name.equals("topConcStateA_A")))
            throw new ErrorSyntax("Transition event not stored in the IDS");

        DashValidation.clearContainers();
    }

    public static void testVarNames() {

        String dashModel = "conc state concState { var_one: none->none var_two: none->none conc state innerConcState {var_three: none->none} }";

        DashModule module = CompUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);

        module.isUnitTest = true;

        System.out.println(module.variableNames.get("concState").get(0));
        System.out.println(module.variableNames.get("concState_innerConcState").get(0));

        if (!module.variableNames.get("concState").get(0).equals("var_one"))
            throw new ErrorSyntax("Outer Conc State variable not stored properly.");
        if (!module.variableNames.get("concState").get(1).equals("var_two"))
            throw new ErrorSyntax("Outer Conc State variable not stored properly.");
        if (!module.variableNames.get("concState_innerConcState").get(0).equals("var_three"))
            throw new ErrorSyntax("Inner Conc State variable not stored properly.");

        DashValidation.clearContainers();
    }


    //CoreDash Unit Tests
    public static void testCoreDashTransitions() {

        String dashModel = "conc state concState { var_one: none trans {do var_one = none} trans trans_two {do var_one = none} default state state_one {trans {do var_one = none}} }";

        DashModule module = CompUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);

        module.isUnitTest = true;

        List<DashTrans> transitions = new ArrayList<DashTrans>();
        for (DashTrans trans : module.transitions.values())
            transitions.add(trans);

        if (transitions.size() < 3)
            throw new ErrorSyntax("Every transition has not been stored.");
        if (transitions.size() > 3)
            throw new ErrorSyntax("More transitions than necessary has been stored.");
        if (!transitions.get(0).modifiedName.equals("concState_t_1"))
            throw new ErrorSyntax("Transition Name not stored correctly.");
        if (!transitions.get(1).modifiedName.equals("concState_trans_two"))
            throw new ErrorSyntax("Transition Name not stored correctly.");
        if (!transitions.get(2).modifiedName.equals("concState_state_one_t_2"))
            throw new ErrorSyntax("Transition Name not stored correctly.");

        DashValidation.clearContainers();
    }

    public static void testTransitionIncompleteCommand() {

        String dashModel = "conc state concState { var_one: none trans {do var_one = none} trans trans_two {do var_one = none} default state state_one {trans {do var_one = none}} }";

        DashModule module = CompUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);

        module.isUnitTest = true;

        List<DashTrans> transitions = new ArrayList<DashTrans>();
        for (DashTrans trans : module.transitions.values()) {
            System.out.println(trans.modifiedName + " fromExpr: " + trans.fromExpr.fromExpr.get(0));
            System.out.println(trans.modifiedName + " gotoExpr: " + trans.gotoExpr.gotoExpr.get(0));
            transitions.add(trans);
        }

        if (transitions.size() < 3)
            throw new ErrorSyntax("Every transition has not been stored.");
        if (transitions.size() > 3)
            throw new ErrorSyntax("More transitions than necessary has been stored.");

        if (!transitions.get(0).fromExpr.fromExpr.get(0).equals("concState"))
            throw new ErrorSyntax("Transition From Expr not stored correctly.");
        if (!transitions.get(0).gotoExpr.gotoExpr.get(0).equals("concState"))
            throw new ErrorSyntax("Transition Goto Expr not stored correctly.");

        if (!transitions.get(1).fromExpr.fromExpr.get(0).equals("concState"))
            throw new ErrorSyntax("Transition From Expr not stored correctly.");
        if (!transitions.get(1).fromExpr.fromExpr.get(0).equals("concState"))
            throw new ErrorSyntax("Transition Goto Expr not stored correctly.");

        if (!transitions.get(2).fromExpr.fromExpr.get(0).equals("concState/state_one"))
            throw new ErrorSyntax("Transition From Expr not stored correctly.");
        if (!transitions.get(2).fromExpr.fromExpr.get(0).equals("concState/state_one"))
            throw new ErrorSyntax("Transition Goto Expr not stored correctly.");


        DashValidation.clearContainers();
    }

    public static void testTransitionAllCommands() {

        String dashModel = "conc state concState { var_one: none event event_one {} default state state_one {} state state_two {} trans {from state_one, state_two on event_one when var_one = none do var_one' = var_one goto state_two send event_one }}";

        DashModule module = CompUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);

        module.isUnitTest = true;

        List<DashTrans> transitions = new ArrayList<DashTrans>();
        for (DashTrans trans : module.transitions.values()) {
            System.out.println(trans.modifiedName + " fromExpr: " + trans.fromExpr.fromExpr.get(0));
            System.out.println(trans.modifiedName + "onExpr: " + trans.onExpr.name);
            System.out.println(trans.modifiedName + "doExpr: " + trans.doExpr.exprList.get(0).toString());
            System.out.println(trans.modifiedName + "whenExpr: " + trans.whenExpr.exprList.get(0).toString());
            System.out.println(trans.modifiedName + "gotoExpr: " + trans.gotoExpr.gotoExpr.get(0));
            System.out.println(trans.modifiedName + "sendExpr: " + trans.sendExpr.name);
            transitions.add(trans);
        }

        if (!transitions.get(0).fromExpr.fromExpr.get(0).equals("concState/state_one"))
            throw new ErrorSyntax("Transition From Expr not stored correctly.");
        if (!transitions.get(0).onExpr.name.equals("concState_event_one"))
            throw new ErrorSyntax("Transition On Expr not stored correctly.");
        if (!transitions.get(0).doExpr.exprList.get(0).toString().equals("var_one' = var_one"))
            throw new ErrorSyntax("Transition do Expr not stored correctly.");
        if (!transitions.get(0).whenExpr.exprList.get(0).toString().equals("var_one = none"))
            throw new ErrorSyntax("Transition when Expr not stored correctly.");
        if (!transitions.get(0).gotoExpr.gotoExpr.get(0).equals("concState/state_two"))
            throw new ErrorSyntax("Transition Goto Expr not stored correctly.");
        if (!transitions.get(0).sendExpr.name.equals("concState_event_one"))
            throw new ErrorSyntax("Transition Send Expr not stored correctly.");

        if (!transitions.get(1).fromExpr.fromExpr.get(0).equals("concState/state_two"))
            throw new ErrorSyntax("Transition From Expr not stored correctly.");
        if (!transitions.get(1).onExpr.name.equals("concState_event_one"))
            throw new ErrorSyntax("Transition On Expr not stored correctly.");
        if (!transitions.get(1).doExpr.exprList.get(0).toString().equals("var_one' = var_one"))
            throw new ErrorSyntax("Transition do Expr not stored correctly.");
        if (!transitions.get(1).whenExpr.exprList.get(0).toString().equals("var_one = none"))
            throw new ErrorSyntax("Transition when Expr not stored correctly.");
        if (!transitions.get(1).gotoExpr.gotoExpr.get(0).equals("concState/state_two"))
            throw new ErrorSyntax("Transition Goto Expr not stored correctly.");
        if (!transitions.get(1).sendExpr.name.equals("concState_event_one"))
            throw new ErrorSyntax("Transition Send Expr not stored correctly.");

        DashValidation.clearContainers();
    }

    public static void testTransitionTemplate() {

        String dashModel = "conc state concState { var_one: none event event_one {} def trans template [s: State, e: Event] {from s, state_two on e when var_one = none do var_one' = var_one goto s send e} default state state_one {} state state_two {} trans{ template[state_one, event_one]} }";

        DashModule module = CompUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);

        module.isUnitTest = true;

        List<DashTrans> transitions = new ArrayList<DashTrans>();
        for (DashTrans trans : module.transitions.values()) {
            transitions.add(trans);
        }

        if (!transitions.get(0).fromExpr.fromExpr.get(0).equals("concState/state_one"))
            throw new ErrorSyntax("Transition From Expr not stored correctly.");
        if (!transitions.get(0).onExpr.name.equals("concState_event_one"))
            throw new ErrorSyntax("Transition On Expr not stored correctly.");
        if (!transitions.get(0).doExpr.exprList.get(0).toString().equals("var_one' = var_one"))
            throw new ErrorSyntax("Transition do Expr not stored correctly.");
        if (!transitions.get(0).whenExpr.exprList.get(0).toString().equals("var_one = none"))
            throw new ErrorSyntax("Transition when Expr not stored correctly.");
        if (!transitions.get(0).gotoExpr.gotoExpr.get(0).equals("concState/state_one"))
            throw new ErrorSyntax("Transition Goto Expr not stored correctly.");
        if (!transitions.get(0).sendExpr.name.equals("concState_event_one"))
            throw new ErrorSyntax("Transition Send Expr not stored correctly.");

        if (!transitions.get(1).fromExpr.fromExpr.get(0).equals("concState/state_two"))
            throw new ErrorSyntax("Transition From Expr not stored correctly.");
        if (!transitions.get(1).onExpr.name.equals("concState_event_one"))
            throw new ErrorSyntax("Transition On Expr not stored correctly.");
        if (!transitions.get(1).doExpr.exprList.get(0).toString().equals("var_one' = var_one"))
            throw new ErrorSyntax("Transition do Expr not stored correctly.");
        if (!transitions.get(1).whenExpr.exprList.get(0).toString().equals("var_one = none"))
            throw new ErrorSyntax("Transition when Expr not stored correctly.");
        if (!transitions.get(1).gotoExpr.gotoExpr.get(0).equals("concState/state_one"))
            throw new ErrorSyntax("Transition Goto Expr not stored correctly.");
        if (!transitions.get(1).sendExpr.name.equals("concState_event_one"))
            throw new ErrorSyntax("Transition Send Expr not stored correctly.");

        DashValidation.clearContainers();
    }

}
