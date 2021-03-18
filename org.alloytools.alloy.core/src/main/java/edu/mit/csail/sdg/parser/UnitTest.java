package edu.mit.csail.sdg.parser;


import java.util.Arrays;
import java.util.List;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;

public class UnitTest {

    static List<String> expectedStateNames = Arrays.asList("topStateA", "topStateB");

    public static void testStates() {

        String dashModel = "conc state concState { " + "default state topStateA { " + "default state innerState{}}" + "state topStateB{}}";

        DashModule module = CompUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);

        //System.out.println("Size of stateNames: " + DASHValidation.stateNames.get("concState").size());


        if (!expectedStateNames.equals(DASHValidation.stateNames.get("concState")))
            throw new ErrorSyntax("Every state has not been stored in the IDS");
        if (!module.states.get("concState_topStateA").states.get(0).name.equals("innerState"))
            throw new ErrorSyntax("Child state has not been stored in the IDS");


        DASHValidation.clearContainers();
    }

    public static void testConcStates() {

        String dashModel = "conc state topConcStateA { conc state innerConcState{  default state A {} } } conc state topConcStateB { default state B{} }";

        DashModule module = CompUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);

        if (!(module.concStates.get("topConcStateA").name.equals("topConcStateA")))
            throw new ErrorSyntax("Top level concurrent state not stored in the IDS");
        if (!(module.concStates.get("topConcStateA").concStates.get(0).name.equals("innerConcState")))
            throw new ErrorSyntax("Child concurrent state not stored in the IDS");
        if (!(module.states.get("topConcStateA_innerConcState_A").name.equals("A")))
            throw new ErrorSyntax("Inner OR state not stored in the IDS");
        if (!(module.concStates.get("topConcStateB").name.equals("topConcStateB")))
            throw new ErrorSyntax("Top level concurrent state not stored in the IDS");

        DASHValidation.clearContainers();
    }

    public static void testTransitions() {

        String dashModel = "conc state topConcStateA { event A{} trans A {on A goto B} default state B {trans B {on A}} }";

        DashModule module = CompUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);

        if (!(module.transitions.get("topConcStateA_A").name.equals("A")))
            throw new ErrorSyntax("Transition not stored in the IDS");
        if (!(module.transitions.get("topConcStateA_B_B").name.equals("B")))
            throw new ErrorSyntax("Transition not stored in the IDS");
        if (!(module.transitions.get("topConcStateA_A").gotoExpr.gotoExpr.get(0).equals("B")))
            throw new ErrorSyntax("Transition event not stored in the IDS");
        if (!(module.transitions.get("topConcStateA_B_B").onExpr.equals("A")))
            throw new ErrorSyntax("Transition event not stored in the IDS");

        DASHValidation.clearContainers();
    }



}
