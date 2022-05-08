package org.alloytools.dash.core;


import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import ca.uwaterloo.watform.ast.DashTrans;
import edu.mit.csail.sdg.ast.Func;
import ca.uwaterloo.watform.transform.CoreDashToAlloy;
import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.DashOptions;
import ca.uwaterloo.watform.transform.DashToCoreDash;
import ca.uwaterloo.watform.parser.DashUtil;
import ca.uwaterloo.watform.parser.DashValidation;

public class DashModelsTest {

    //Dash Parser Unit Tests
    @Test
    public void testStates() throws Exception {
        String dashModel = "conc state concState { default state topStateA { default state innerState{}} state topStateB{}}";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);

        if (module.states.get("concState_topStateA") == null)
            throw new Exception("Every state has not been stored in the IDS");
        if (module.states.get("concState_topStateA_innerState") == null)
            throw new Exception("Every state has not been stored in the IDS");
        if (module.states.get("concState_topStateB") == null)
            throw new Exception("Every state has not been stored in the IDS");
        if (!module.states.get("concState_topStateA").states.get(0).name.equals("innerState"))
            throw new Exception("Child state has not been stored in the IDS");

        DashValidation.clearContainers();
    }

    @Test
    public void testConcStates() throws Exception {

        String dashModel = "conc state topConcStateA { conc state innerConcState{  default state A {} } } conc state topConcStateB { default state B{} }";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(module);

        if (!(module.concStates.get("topConcStateA").name.equals("topConcStateA")))
            throw new Exception("Top level concurrent state not stored in the IDS");
        if (!(module.concStates.get("topConcStateA").concStates.get(0).name.equals("innerConcState")))
            throw new Exception("Child concurrent state not stored in the IDS");
        if (!(module.states.get("topConcStateA_innerConcState_A").name.equals("A")))
            throw new Exception("Inner OR state not stored in the IDS");
        if (!(module.concStates.get("topConcStateB").name.equals("topConcStateB")))
            throw new Exception("Top level concurrent state not stored in the IDS");

        DashValidation.clearContainers();
    }
    
    @Test
    public void testParamConcStates() throws Exception {

        String dashModel = "conc state topConcStateA [PID1] { default state A {} } conc state topConcStateB [PID2] { default state B{} }";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(module);

        if (!(module.concStates.get("topConcStateA").name.equals("topConcStateA")))
            throw new Exception("Top level concurrent state not stored in the IDS");
        if (!(module.concStates.get("topConcStateB").name.equals("topConcStateB")))
            throw new Exception("Top level concurrent state not stored in the IDS");
        
        if (!(module.concStates.get("topConcStateA").param.equals("PID1")))
            throw new Exception("Top level concurrent (topConcStateA) parameter not stored properly." + " Param: " + module.concStates.get("topConcStateA").param);
        if (!(module.concStates.get("topConcStateB").param.equals("PID2")))
            throw new Exception("Top level concurrent (topConcStateB) parameter not stored properly.");

        DashValidation.clearContainers();
    }

    @Test
    public void testVarRefs() throws Exception {

        String dashModel = "conc state Parent {\n"
        		+ "	conc state Child1 [PID1] {\n"
        		+ "		var1: lone Int\n"
        		+ "		default state S0 {\n"
        		+ "			trans T0 {\n"
        		+ "				goto S1\n"
        		+ "				do {\n"
        		+ "					one p: PID2 | Child2[p]/var2' = {none}\n"
        		+ "				}\n"
        		+ "			}\n"
        		+ "		}\n"
        		+ "		state S1 {}\n"
        		+ "	}\n"
        		+ "\n"
        		+ "	conc state Child2 [PID2] {\n"
        		+ "		var2: lone Int\n"
        		+ "		default state S0 {\n"
        		+ "			trans T0 {\n"
        		+ "				do {\n"
        		+ "					one p: PID1 | Child1[p]/var1' = {none}\n"
        		+ "				}\n"
        		+ "				goto S1\n"
        		+ "			}\n"
        		+ "		}\n"
        		+ "		state S1 {}\n"
        		+ "	}\n"
        		+ "}\n"
        		+ "";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(module);
        CoreDashToAlloy.convertToAlloyAST(module);
        
        List<Func> funcs0 = new ArrayList<Func>();
        List<Func> funcs1 = new ArrayList<Func>();
        
        for (String name : module.funcs.keySet()) {
            if (name.equals("pos_Parent_Child1_S0_T0"))
                funcs0 = module.funcs.get(name);
            if (name.equals("pos_Parent_Child2_S0_T0"))
                funcs1 = module.funcs.get(name);
        }
         
        String expectedOutput1 = "one p | AND[p.s_next.Parent_Child2_var2 = none";
        String expectedOutput2 = "one p | AND[p.s_next.Parent_Child1_var1 = none";

        if (!(funcs0.get(0).getBody().toString().contains(expectedOutput1)))
            throw new Exception("Post-Conditions Not Stored Properly (1)." + " Expected: " + funcs0.get(0).getBody().toString());
        if (!(funcs1.get(0).getBody().toString().contains(expectedOutput2)))
            throw new Exception("Post-Conditions Not Stored Properly (2)." + " Expected: " + funcs1.get(0).getBody().toString());

        DashValidation.clearContainers();
    }
   
    @Test
    public void testTransitions() throws Exception {

        String dashModel = "conc state topConcStateA { event A{} trans A {on A goto B} default state B {trans B {on A}} }";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(module);

        if (!(module.transitions.get("topConcStateA_A").name.equals("A")))
            throw new Exception("Transition not stored in the IDS");
        if (!(module.transitions.get("topConcStateA_B_B").name.equals("B")))
            throw new Exception("Transition not stored in the IDS");
        if (!(module.transitions.get("topConcStateA_A").gotoExpr.gotoExpr.get(0).equals("topConcStateA_B")))
            throw new Exception("Transition goto not stored in the IDS" + " Expected: " + module.transitions.get("topConcStateA_A").gotoExpr.gotoExpr.get(0));
        if (!(module.transitions.get("topConcStateA_B_B").onExpr.name.equals("topConcStateA_A")))
            throw new Exception("Transition event not stored in the IDS");

        DashValidation.clearContainers();
    }

    @Test
    public void testVarNames() throws Exception {

        String dashModel = "conc state concState { var_one: none->none var_two: none->none conc state innerConcState {var_three: none->none} }";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);

        if (!module.variableNames.get("concState").get(0).equals("var_one"))
            throw new Exception("Outer Conc State variable not stored properly.");
        if (!module.variableNames.get("concState").get(1).equals("var_two"))
            throw new Exception("Outer Conc State variable not stored properly.");
        if (!module.variableNames.get("concState_innerConcState").get(0).equals("var_three"))
            throw new Exception("Inner Conc State variable not stored properly.");

        DashValidation.clearContainers();
    }


    //CoreDash Unit Tests
     @Test
    public void testCoreDashTransitions() throws Exception {

        String dashModel = "conc state concState { var_one: none trans {do var_one = none} trans trans_two {do var_one = none} default state state_one {trans {do var_one = none}} }";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(module);


        List<DashTrans> transitions = new ArrayList<DashTrans>();
        for (DashTrans trans : module.transitions.values())
            transitions.add(trans);

        if (transitions.size() < 3)
            throw new Exception("Every transition has not been stored.");
        if (transitions.size() > 3)
            throw new Exception("More transitions than necessary has been stored.");
        if (!transitions.get(0).modifiedName.equals("concState_t_1"))
            throw new Exception("Transition Name not stored correctly.");
        if (!transitions.get(1).modifiedName.equals("concState_trans_two"))
            throw new Exception("Transition Name not stored correctly.");
        if (!transitions.get(2).modifiedName.equals("concState_state_one_t_2"))
            throw new Exception("Transition Name not stored correctly.");

        DashValidation.clearContainers();
    }

    @Test
    public void testTransitionIncompleteCommand() throws Exception {

        String dashModel = "conc state concState { var_one: none trans {do var_one = none} trans trans_two {do var_one = none} default state state_one {trans {do var_one = none}} }";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(module);

        List<DashTrans> transitions = new ArrayList<DashTrans>();
        for (DashTrans trans : module.transitions.values()) {
            transitions.add(trans);
        }

        if (transitions.size() < 3)
            throw new Exception("Every transition has not been stored.");
        if (transitions.size() > 3)
            throw new Exception("More transitions than necessary has been stored.");

        if (!transitions.get(0).fromExpr.fromExpr.get(0).equals("concState"))
            throw new Exception("Transition From Expr not stored correctly.");
        if (!transitions.get(0).gotoExpr.gotoExpr.get(0).equals("concState"))
            throw new Exception("Transition Goto Expr not stored correctly.");

        if (!transitions.get(1).fromExpr.fromExpr.get(0).equals("concState"))
            throw new Exception("Transition From Expr not stored correctly.");
        if (!transitions.get(1).fromExpr.fromExpr.get(0).equals("concState"))
            throw new Exception("Transition Goto Expr not stored correctly.");

        if (!transitions.get(2).fromExpr.fromExpr.get(0).equals("concState/state_one"))
            throw new Exception("Transition From Expr not stored correctly.");
        if (!transitions.get(2).fromExpr.fromExpr.get(0).equals("concState/state_one"))
            throw new Exception("Transition Goto Expr not stored correctly.");


        DashValidation.clearContainers();
    }

    @Test
    public void testTransitionAllCommands() throws Exception {

        String dashModel = "conc state concState { var_one: none event event_one {} default state state_one {} state state_two {} trans {from state_one, state_two on event_one when var_one = none do var_one' = var_one goto state_two send event_one }}";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(module);

        List<DashTrans> transitions = new ArrayList<DashTrans>();
        for (DashTrans trans : module.transitions.values()) {
            transitions.add(trans);
        }

        if (!transitions.get(0).fromExpr.fromExpr.get(0).equals("concState_state_one"))
            throw new Exception("Transition From Expr not stored correctly.");
        if (!transitions.get(0).onExpr.name.equals("concState_event_one"))
            throw new Exception("Transition On Expr not stored correctly.");
        if (!transitions.get(0).doExpr.exprList.get(0).toString().equals("var_one' = var_one"))
            throw new Exception("Transition do Expr not stored correctly.");
        if (!transitions.get(0).whenExpr.exprList.get(0).toString().equals("var_one = none"))
            throw new Exception("Transition when Expr not stored correctly. Expected is: var_one = none, Actual is: " + transitions.get(0).whenExpr.exprList.get(0).toString());
        if (!transitions.get(0).gotoExpr.gotoExpr.get(0).equals("concState_state_two"))
            throw new Exception("Transition Goto Expr not stored correctly.");
        if (!transitions.get(0).sendExpr.name.equals("concState_event_one"))
            throw new Exception("Transition Send Expr not stored correctly.");

        if (!transitions.get(1).fromExpr.fromExpr.get(0).equals("concState_state_two"))
            throw new Exception("Transition From Expr not stored correctly.");
        if (!transitions.get(1).onExpr.name.equals("concState_event_one"))
            throw new Exception("Transition On Expr not stored correctly.");
        if (!transitions.get(1).doExpr.exprList.get(0).toString().equals("var_one' = var_one"))
            throw new Exception("Transition do Expr not stored correctly.");
        if (!transitions.get(1).whenExpr.exprList.get(0).toString().equals("var_one = none"))
            throw new Exception("Transition when Expr not stored correctly. Expected is: var_one = none, Actual is: " + transitions.get(1).whenExpr.exprList.get(0).toString());
        if (!transitions.get(1).gotoExpr.gotoExpr.get(0).equals("concState_state_two"))
            throw new Exception("Transition Goto Expr not stored correctly.");
        if (!transitions.get(1).sendExpr.name.equals("concState_event_one"))
            throw new Exception("Transition Send Expr not stored correctly.");

        DashValidation.clearContainers();
    }

    @Test
    public void testTransitionTemplate() throws Exception {

        String dashModel = "conc state concState { var_one: none event event_one {} def trans template [s: State, e: Event] {from s, state_two on e when var_one = none do var_one' = var_one goto s send e} default state state_one {} state state_two {} trans{ template[state_one, event_one]} }";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(module);

        List<DashTrans> transitions = new ArrayList<DashTrans>();
        for (DashTrans trans : module.transitions.values()) {
            transitions.add(trans);
        }

        if (!transitions.get(0).fromExpr.fromExpr.get(0).equals("concState_state_one"))
            throw new Exception("Transition From Expr not stored correctly.");
        if (!transitions.get(0).onExpr.name.equals("concState_event_one"))
            throw new Exception("Transition On Expr not stored correctly.");
        if (!transitions.get(0).doExpr.exprList.get(0).toString().equals("var_one' = var_one"))
            throw new Exception("Transition do Expr not stored correctly.");
        if (!transitions.get(0).whenExpr.exprList.get(0).toString().equals("var_one = none"))
            throw new Exception("Transition when Expr not stored correctly.");
        if (!transitions.get(0).gotoExpr.gotoExpr.get(0).equals("concState_state_one"))
            throw new Exception("Transition Goto Expr not stored correctly.");
        if (!transitions.get(0).sendExpr.name.equals("concState_event_one"))
            throw new Exception("Transition Send Expr not stored correctly.");

        if (!transitions.get(1).fromExpr.fromExpr.get(0).equals("concState_state_two"))
            throw new Exception("Transition From Expr not stored correctly.");
        if (!transitions.get(1).onExpr.name.equals("concState_event_one"))
            throw new Exception("Transition On Expr not stored correctly.");
        if (!transitions.get(1).doExpr.exprList.get(0).toString().equals("var_one' = var_one"))
            throw new Exception("Transition do Expr not stored correctly.");
        if (!transitions.get(1).whenExpr.exprList.get(0).toString().equals("var_one = none"))
            throw new Exception("Transition when Expr not stored correctly.");
        if (!transitions.get(1).gotoExpr.gotoExpr.get(0).equals("concState_state_one"))
            throw new Exception("Transition Goto Expr not stored correctly.");
        if (!transitions.get(1).sendExpr.name.equals("concState_event_one"))
            throw new Exception("Transition Send Expr not stored correctly.");

        DashValidation.clearContainers();
    }

    //CoreDash to Alloy AST Unit Tests
    
    @Test
    public void testPredicateNames() throws Exception {

        String dashModel = "conc state topConcStateA { event envA{} trans A {on envA goto B} default state B {trans B {on envA}} }";
        DashOptions.outputDir = "test.dsh";

        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(module);
        DashValidation.validateDashModel(module);
        CoreDashToAlloy.convertToAlloyAST(module);


        if (!(module.funcs.keySet().contains("pre_topConcStateA_A")))
            throw new Exception("Pre-Condition Predicate Not Stored Correctly.");
        if (!(module.funcs.keySet().contains("pos_topConcStateA_A")))
            throw new Exception("Post-Condition Predicate Not Stored Correctly.");
        if (!(module.funcs.keySet().contains("topConcStateA_A")))
            throw new Exception("Trans Name Predicate Not Stored Correctly.");
        if (!(module.funcs.keySet().contains("semantics_topConcStateA_A")))
            throw new Exception("Semantics Predicate Not Stored Correctly.");

        if (!(module.funcs.keySet().contains("pre_topConcStateA_B_B")))
            throw new Exception("Pre-Condition Predicate Not Stored Correctly.");
        if (!(module.funcs.keySet().contains("pos_topConcStateA_B_B")))
            throw new Exception("Post-Condition Predicate Not Stored Correctly.");
        if (!(module.funcs.keySet().contains("topConcStateA_B_B")))
            throw new Exception("Trans Name Predicate Not Stored Correctly.");
        if (!(module.funcs.keySet().contains("semantics_topConcStateA_B_B")))
            throw new Exception("Semantics Predicate Not Stored Correctly.");

        if (!(module.funcs.keySet().contains("init")))
            throw new Exception("Init Predicate Not Stored Correctly.");
        if (!(module.funcs.keySet().contains("small_step")))
            throw new Exception("small_step Name Predicate Not Stored Correctly.");
        if (!(module.funcs.keySet().contains("equals")))
            throw new Exception("equals Predicate Not Stored Correctly.");
        if (!(module.funcs.keySet().contains("path")))
            throw new Exception("path Predicate Not Stored Correctly.");

        DashValidation.clearContainers();
    }

    @Test
    public void testSignatureNames() throws Exception {
        String dashModel = "conc state topConcStateA { event envA{} trans A {on envA goto B} default state B {trans B {on envA}} }";
        DashOptions.outputDir = "test.dsh";

        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(module);
        DashValidation.validateDashModel(module);
        CoreDashToAlloy.convertToAlloyAST(module);

        if (!(module.sigs.keySet().contains("Snapshot")))
            throw new Exception("Signature Name Not Stored Correctly.");
        if (!(module.sigs.keySet().contains("SystemState")))
            throw new Exception("Signature Name Not Stored Correctly.");
        if (!(module.sigs.keySet().contains("topConcStateA")))
            throw new Exception("Signature Name Not Stored Correctly.");
        if (!(module.sigs.keySet().contains("topConcStateA_B")))
            throw new Exception("Signature Name Not Stored Correctly.");
        if (!(module.sigs.keySet().contains("topConcStateA_envA")))
            throw new Exception("Signature Name Not Stored Correctly.");
        if (!(module.sigs.keySet().contains("topConcStateA_A")))
            throw new Exception("Signature Name Not Stored Correctly.");
        if (!(module.sigs.keySet().contains("topConcStateA_B_B")))
            throw new Exception("Signature Name Not Stored Correctly.");

        DashValidation.clearContainers();
    }

    @Test
    public void testPreCondPred() throws Exception {
        String dashModel = "conc state concState { var_one: none event envA {} trans A {from stateA on envA when var_one = none} default state stateA {}}";
        DashOptions.outputDir = "test.dsh";

        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(module);
        DashValidation.validateDashModel(module);
        CoreDashToAlloy.convertToAlloyAST(module);

        List<Func> funcs = new ArrayList<Func>();

        for (String name : module.funcs.keySet()) {
            if (name.equals("pre_concState_A"))
                funcs = module.funcs.get(name);
        }

        String expectedOutput = "AND[concState_stateA in s.conf, concState_envA in s.events & EnvironmentEvent, s.concState_var_one = none]";

        if (!expectedOutput.equals(funcs.get(0).getBody().toString()))
            throw new Exception("Pre-Conditions Not Stored Properly.");

        DashValidation.clearContainers();
    }

    @Test
    public void testPosCondPred() throws Exception {
        String dashModel = "conc state concState { var_one: some EventLabel event envA {} trans A {from stateA on envA when var_one = none} default state stateA {}}";
        DashOptions.outputDir = "test.dsh";

        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(module);
        DashValidation.validateDashModel(module);
        CoreDashToAlloy.convertToAlloyAST(module);

        List<Func> funcs = new ArrayList<Func>();

        for (String name : module.funcs.keySet()) {
            if (name.equals("pos_concState_A"))
                funcs = module.funcs.get(name);
        }

        String expectedOutput = "AND[s_next.conf = s.conf - concState_stateA + concState_stateA, s_next.concState_var_one = s.concState_var_one, no s_next.events & InternalEvent]";

        if (!expectedOutput.equals(funcs.get(0).getBody().toString())) {
            throw new Exception("Post-Conditions Not Stored Properly. Expected: " + expectedOutput + " Actual: " + funcs.get(0).getBody().toString());
        }

        DashValidation.clearContainers();
    }
    
    
    @Test
    public void testPosCondPredWithHierarchy() throws Exception {
        String dashModel = "conc state concState { var_one: one EventLabel event envA {} conc state inner{ default state stateA{} trans A {from stateA on envA when var_one = none}  trans B {from stateA on envA do var_one' = none} } }";
        DashOptions.outputDir = "test.dsh";

        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(module);
        DashValidation.validateDashModel(module);
        CoreDashToAlloy.convertToAlloyAST(module);

        List<Func> funcs = new ArrayList<Func>();

        for (String name : module.funcs.keySet()) {
            if (name.equals("pos_concState_inner_A"))
                funcs = module.funcs.get(name);
        }

        String expectedOutput = "AND[s_next.conf = s.conf - concState_inner_stateA + concState_inner_stateA, s_next.concState_var_one = s.concState_var_one, (none.concState_inner_A.s_next.s.testIfNextStable => AND[s_next.stable = True, (s.stable = True => no s_next.events & InternalEvent else no s_next.events & InternalEvent - InternalEvent & s.events)] else AND[s_next.stable = False, (s.stable = True => AND[s_next.events & InternalEvent = none, s_next.events & EnvironmentEvent = s.events & EnvironmentEvent] else s_next.events = s.events + none)])]";
        
        if (!expectedOutput.equals(funcs.get(0).getBody().toString())) {
            throw new Exception("Post-Conditions Not Stored Properly. Expected: " + expectedOutput + " Actual: " + funcs.get(0).getBody().toString());
        }

        DashValidation.clearContainers();
    }
    
    @Test
    public void testVarRefConstraints() throws Exception {

        String dashModel = "conc state Parent {\n"
        		+ "	conc state Child1 [PID1] {\n"
        		+ "		var1: lone Int\n"
        		+ "		default state S0 {\n"
        		+ "			trans T0 {\n"
        		+ "				goto S1\n"
        		+ "				do {\n"
        		+ "					var1' = {none}\n"
        		+ "					one p: PID2 | Child2[p]/var2' = {none}\n"
        		+ "				}\n"
        		+ "			}\n"
        		+ "		}\n"
        		+ "		state S1 {}\n"
        		+ "	}\n"
        		+ "\n"
        		+ "	conc state Child2 [PID2] {\n"
        		+ "		var2: lone Int\n"
        		+ "		default state S0 {\n"
        		+ "			trans T0 {\n"
        		+ "				do {	\n"
        		+ "					var2' = {none}\n"
        		+ "					one p: PID1 | Child1[p]/var1' = {none}\n"
        		+ "				}\n"
        		+ "				goto S1\n"
        		+ "			}\n"
        		+ "		}\n"
        		+ "		state S1 {}\n"
        		+ "	}\n"
        		+ "}\n"
        		+ "";
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(module);
        CoreDashToAlloy.convertToAlloyAST(module);
        
        List<Func> funcs0 = new ArrayList<Func>();
        List<Func> funcs1 = new ArrayList<Func>();
        
        for (String name : module.funcs.keySet()) {
            if (name.equals("pos_Parent_Child1_S0_T0"))
                funcs0 = module.funcs.get(name);
            if (name.equals("pos_Parent_Child2_S0_T0"))
                funcs1 = module.funcs.get(name);
        }
         
        String expectedOutput1 = "(all quant | quant . s_next.Parent_Child2_var2 = quant . s.Parent_Child2_var2)]), (all quant | quant.s_next.Parent_Child1_var1 = quant.s.Parent_Child1_var1)";
        String expectedOutput2 = "(all quant | quant . s_next.Parent_Child1_var1 = quant . s.Parent_Child1_var1)]), (all quant | quant.s_next.Parent_Child2_var2 = quant.s.Parent_Child2_var2)";

        if (!(funcs0.get(0).getBody().toString().contains(expectedOutput1)))
            throw new Exception("Post-Conditions Not Stored Properly (1)." + " Expected: " + funcs0.get(0).getBody().toString());
        if (!(funcs1.get(0).getBody().toString().contains(expectedOutput2)))
            throw new Exception("Post-Conditions Not Stored Properly (2)." + " Expected: " + funcs1.get(0).getBody().toString());

        DashValidation.clearContainers();
    }
    
    @Test
    public void testBufferInPostCond() throws Exception {

        String dashModel = "conc state Parent {\n"
        		+ "	conc state Child1 [PID1] {\n"
        		+ "		buf1: buf[PID1]\n"
        		+ "		default state S0 {\n"
        		+ "			trans T0 {\n"
        		+ "				goto S1\n"
        		+ "				do {\n"
        		+ "					buf1.add[this]\n"
        		+ "					one p: PID2 | Child2[p]/buf2.add[p]\n"
        		+ "				}\n"
        		+ "			}\n"
        		+ "		}\n"
        		+ "		state S1 {}\n"
        		+ "	}\n"
        		+ "\n"
        		+ "	conc state Child2 [PID2] {\n"
        		+ "		buf2: buf[PID2]\n"
        		+ "		default state S0 {\n"
        		+ "			trans T0 {\n"
        		+ "				do {	\n"
        		+ "					buf2.add[this]\n"
        		+ "					one p: PID1 | Child1[p]/buf1.add[p]\n"
        		+ "				}\n"
        		+ "				goto S1\n"
        		+ "			}\n"
        		+ "		}\n"
        		+ "		state S1 {}\n"
        		+ "	}\n"
        		+ "}\n"
        		+ "";
        
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(module);
        CoreDashToAlloy.convertToAlloyAST(module);
        
        List<Func> funcs0 = new ArrayList<Func>();
        List<Func> funcs1 = new ArrayList<Func>();
        
        for (String name : module.funcs.keySet()) {
            if (name.equals("pos_Parent_Child1_S0_T0"))
                funcs0 = module.funcs.get(name);
            if (name.equals("pos_Parent_Child2_S0_T0"))
                funcs1 = module.funcs.get(name);
        }
         
        String expectedOutput1 = "p.p.s_next.Parent_Child1_buf1.p.s . Parent_Child1_buf1.add, (one p | AND[p.p.s_next.Parent_Child2_buf2.p.s.Parent_Child2_buf2.add, (all quant | quant . s_next.Parent_Child2_buf2 = quant . s.Parent_Child2_buf2)]), (all quant | quant.s_next.Parent_Child1_buf1 = quant.s.Parent_Child1_buf1)";
        String expectedOutput2 = "p.p.s_next.Parent_Child2_buf2.p.s . Parent_Child2_buf2.add, (one p | AND[p.p.s_next.Parent_Child1_buf1.p.s.Parent_Child1_buf1.add, (all quant | quant . s_next.Parent_Child1_buf1 = quant . s.Parent_Child1_buf1)]), (all quant | quant.s_next.Parent_Child2_buf2 = quant.s.Parent_Child2_buf2)";

        if (!(funcs0.get(0).getBody().toString().contains(expectedOutput1)))
            throw new Exception("Post-Conditions Not Stored Properly (1)." + " Expected: " + funcs0.get(0).getBody().toString());
        if (!(funcs1.get(0).getBody().toString().contains(expectedOutput2)))
            throw new Exception("Post-Conditions Not Stored Properly (2)." + " Expected: " + funcs1.get(0).getBody().toString());

        DashValidation.clearContainers();
    }
    
    @Test
    public void testBufferDataStructure() throws Exception {

        String dashModel = "conc state Parent {\n"
        		+ "	conc state Child1 [PID1] {\n"
        		+ "		buf1: buf[PID1]\n"
        		+ "		default state S0 {\n"
        		+ "			trans T0 {\n"
        		+ "				goto S1\n"
        		+ "				do {\n"
        		+ "					buf1.add[this]\n"
        		+ "					one p: PID2 | Child2[p]/buf2.add[p]\n"
        		+ "				}\n"
        		+ "			}\n"
        		+ "		}\n"
        		+ "		state S1 {}\n"
        		+ "	}\n"
        		+ "\n"
        		+ "	conc state Child2 [PID2] {\n"
        		+ "		buf2: buf[PID2]\n"
        		+ "		default state S0 {\n"
        		+ "			trans T0 {\n"
        		+ "				do {	\n"
        		+ "					buf2.add[this]\n"
        		+ "					one p: PID1 | Child1[p]/buf1.add[p]\n"
        		+ "				}\n"
        		+ "				goto S1\n"
        		+ "			}\n"
        		+ "		}\n"
        		+ "		state S1 {}\n"
        		+ "	}\n"
        		+ "}\n"
        		+ "";
        
        DashOptions.outputDir = "test.dsh";
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(module);
        CoreDashToAlloy.convertToAlloyAST(module);
        
        List<String> buffers = new ArrayList<String>();
        List<String> bufferElems = new ArrayList<String>();
        
        for (String name : module.bufferNameToElem.keySet()) {
        	buffers.add(name);
        	bufferElems.add(module.bufferNameToElem.get(name));
        }
         
        if (!(buffers.get(0).equals("Parent_Child1_buf1")))
            throw new Exception("Buffer Not Stored Properly." + " Expected: " + buffers.get(0));
        if (!(buffers.get(1).equals("Parent_Child2_buf2")))
            throw new Exception("Buffer Not Stored Properly." + " Expected: " + buffers.get(0));
        if (!(bufferElems.get(0).equals("PID1")))
            throw new Exception("Buffer Element Not Stored Properly." + " Expected: " + buffers.get(0));
        if (!(bufferElems.get(1).equals("PID2")))
            throw new Exception("Buffer Element Not Stored Properly." + " Expected: " + buffers.get(0));
        
        
        DashValidation.clearContainers();
    }
    
    
    @Test
    public void testEnabledAfterNextStep() throws Exception {
        String dashModel = "conc state concState { var_one: one EventLabel event envA {} conc state inner{ default state stateA{} trans A {from stateA on envA when var_one = none}  trans B {from stateA on envA do var_one' = none} } }";
        DashOptions.outputDir = "test.dsh";

        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(module);
        DashValidation.validateDashModel(module);
        CoreDashToAlloy.convertToAlloyAST(module);

        List<Func> funcs = new ArrayList<Func>();

        for (String name : module.funcs.keySet()) {
            if (name.equals("enabledAfterStep_concState_inner_A"))
                funcs = module.funcs.get(name);
        }

        String expectedOutput = "AND[concState_inner_stateA in s.conf, s.concState_var_one = none, (_s.stable = True => AND[no t & concState_inner_A + concState_inner_B, concState_envA in _s.events & EnvironmentEvent + genEvents] else AND[no _s.taken + t & concState_inner_A + concState_inner_B, concState_envA in _s.events + genEvents])]";

        if (!expectedOutput.equals(funcs.get(0).getBody().toString()))
            throw new Exception("Enabled After Not Stored Properly.");

        DashValidation.clearContainers();
    }
    
    @Test
    public void testTestIfNextStep() throws Exception {
        String dashModel = "conc state concState { var_one: one EventLabel event envA {} conc state inner{ default state stateA{} trans A {from stateA on envA when var_one = none}  trans B {from stateA on envA do var_one' = none} } }";
        DashOptions.outputDir = "test.dsh";

        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(module);
        DashValidation.validateDashModel(module);
        CoreDashToAlloy.convertToAlloyAST(module);

        List<Func> funcs = new ArrayList<Func>();

        for (String name : module.funcs.keySet()) {
            if (name.equals("testIfNextStable"))
                funcs = module.funcs.get(name);
        }

        String expectedOutput = "AND[! genEvents.t.s_next.s.enabledAfterStep_concState_inner_A, ! genEvents.t.s_next.s.enabledAfterStep_concState_inner_B]";

        if (!expectedOutput.equals(funcs.get(0).getBody().toString()))
            throw new Exception("TestIfNext After Not Stored Properly.");

        DashValidation.clearContainers();
    }
    
    @Test
    public void testTestIsEnabled() throws Exception {
        String dashModel = "conc state concState { var_one: one EventLabel event envA {} conc state inner{ default state stateA{} trans A {from stateA on envA when var_one = none}  trans B {from stateA on envA do var_one' = none} } }";
        DashOptions.outputDir = "test.dsh";

        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(module);
        DashValidation.validateDashModel(module);
        CoreDashToAlloy.convertToAlloyAST(module);

        List<Func> funcs = new ArrayList<Func>();

        for (String name : module.funcs.keySet()) {
            if (name.equals("isEnabled"))
                funcs = module.funcs.get(name);
        }

        String expectedOutput = "OR[s.pre_concState_inner_A, s.pre_concState_inner_B]";

        if (!expectedOutput.equals(funcs.get(0).getBody().toString()))
            throw new Exception("TestIfNext After Not Stored Properly.");

        DashValidation.clearContainers();
    }


    @Test
    public void testSemanticsPred() throws Exception {
        String dashModel = "conc state concState { var_one: some EventLabel event envA {} trans A {from stateA on envA when var_one = none} default state stateA {}}";
        DashOptions.outputDir = "test.dsh";

        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(module);
        DashValidation.validateDashModel(module);
        CoreDashToAlloy.convertToAlloyAST(module);

        List<Func> funcs = new ArrayList<Func>();

        for (String name : module.funcs.keySet()) {
            if (name.equals("semantics_concState_A"))
                funcs = module.funcs.get(name);
        }

        String expectedOutput = "s_next.taken = concState_A";

        if (!expectedOutput.equals(funcs.get(0).getBody().toString()))
            throw new Exception("Semantics Not Stored Properly.");

        DashValidation.clearContainers();
    }

    @Test
    public void testInitPred() throws Exception {
        String dashModel = "conc state concState { var_one: some EventLabel event envA {} trans A {from stateA on envA when var_one = none} default state stateA {}}";
        DashOptions.outputDir = "test.dsh";

        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(module);
        DashValidation.validateDashModel(module);
        CoreDashToAlloy.convertToAlloyAST(module);

        List<Func> funcs = new ArrayList<Func>();

        for (String name : module.funcs.keySet()) {
            if (name.equals("init"))
                funcs = module.funcs.get(name);
        }

        String expectedOutput = "AND[s.conf = concState_stateA, no s.taken, no s.events & InternalEvent]";

        if (!expectedOutput.equals(funcs.get(0).getBody().toString()))
            throw new Exception("Init Not Stored Properly.");

        DashValidation.clearContainers();
    }

    @Test
    public void testEqualsPred() throws Exception {
        String dashModel = "conc state concState { var_one: some EventLabel event envA {} trans A {from stateA on envA when var_one = none} default state stateA {}}";
        DashOptions.outputDir = "test.dsh";

        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(module);
        DashValidation.validateDashModel(module);
        CoreDashToAlloy.convertToAlloyAST(module);

        List<Func> funcs = new ArrayList<Func>();

        for (String name : module.funcs.keySet()) {
            if (name.equals("equals"))
                funcs = module.funcs.get(name);
        }

        String expectedOutput = "AND[s_next.conf = s.conf, s_next.events = s.events, s_next.taken = s.taken, s_next.concState_var_one = s.concState_var_one]";

        if (!expectedOutput.equals(funcs.get(0).getBody().toString()))
            throw new Exception("Equals Predicate Not Stored Properly.");

        DashValidation.clearContainers();
    }


    @Test
    public void testModelFactTraces() throws Exception {
        String dashModel = "conc state concState { var_one: some EventLabel event envA {} trans A {from stateA on envA when var_one = none} default state stateA {}}";
        DashOptions.outputDir = "test.dsh";

        DashOptions.ctlModelChecking = false;
        DashOptions.generateTraces = true;
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(module);
        DashValidation.validateDashModel(module);
        CoreDashToAlloy.convertToAlloyAST(module);

        String expectedOutput = "AND[snapshot/first.init, (all s | ! s in snapshot/last => s . next.s.small_step)]";

        if (!expectedOutput.equals(module.facts.get(1).b.toString()))
            throw new Exception("Fact Not Stored Properly." + " Actual: " + module.facts.get(1).b.toString());

        DashValidation.clearContainers();
    }
    
    @Test
    public void testModelFactCTL() throws Exception {
        String dashModel = "conc state concState { var_one: one EventLabel event envA {} conc state inner{ default state stateA{} trans A {from stateA on envA when var_one = none}  trans B {from stateA on envA do var_one' = none} } }";
        DashOptions.outputDir = "test.dsh";

        DashOptions.ctlModelChecking = true;
        DashOptions.generateTraces = false;
        
        DashModule module = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(module);
        DashValidation.validateDashModel(module);
        CoreDashToAlloy.convertToAlloyAST(module);

        String expectedOutput = "AND[(all s | s in ks_s0 <=> s.init), (all s,s_next | s -> s_next in ks_sigma <=> s_next.s.small_step)]";

        System.out.println("Actual  : " + module.facts.get(0).b.toString());
        System.out.println("Expected: " + expectedOutput);
        
        if (!expectedOutput.equals(module.facts.get(2).b.toString()))
        	throw new Exception("Fact Not Stored Properly." + " Actual: " + module.facts.get(2).b.toString());

        DashValidation.clearContainers();
    }
}
