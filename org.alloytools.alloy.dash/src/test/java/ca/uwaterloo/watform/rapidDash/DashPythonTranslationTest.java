package ca.uwaterloo.watform.rapidDash;


import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.DashUtil;
import ca.uwaterloo.watform.transform.DashToCoreDash;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import org.junit.Test;

import java.util.List;
import java.util.stream.Collectors;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;


public class DashPythonTranslationTest {
    private long findStateOccurncesInTranslation(DashPythonTranslation translation, String stateName) {
        return translation.getStates().stream().filter(state -> state.getName().equals(stateName)).count();
    }

    private DashPythonTranslation.State findStateInTranslation(DashPythonTranslation translation, String stateName) {
        return translation.getStates().stream().filter(state -> state.getName().equals(stateName)).findAny().get();
    }

    @Test
    public void testStates() throws Exception {
        String dashModel = "conc state concState { default state topStateA { default state innerState{}} state topStateB{}}";
        DashModule dashModule = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(dashModule);
        DashPythonTranslation translation = new DashPythonTranslation(dashModule);

        assertEquals(4, translation.getStates().size());
        assertEquals(1, findStateOccurncesInTranslation(translation, "concState_topStateA_innerState"));
        assertEquals(1, findStateOccurncesInTranslation(translation, "concState_topStateB"));
        assertEquals(1, findStateOccurncesInTranslation(translation, "concState_topStateA"));
        assertEquals(1, findStateOccurncesInTranslation(translation, "concState"));
    }

    @Test
    public void testTransitions() throws Exception {
        String dashModel = "conc state topConcStateA { event A{} default state s1{} state s2{} trans t1 {on A goto s1} trans t2 {on A goto s2} }";

        DashModule dashModule = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(dashModule);

        DashPythonTranslation translation = new DashPythonTranslation(dashModule);

        List<String> transitionNames = findStateInTranslation(translation, "topConcStateA")
                .getTransitions().stream().map(transition -> transition.getTransName()).collect(Collectors.toList());
        assertEquals(2, findStateInTranslation(translation, "topConcStateA").getTransitions().size());
        assertTrue(transitionNames.contains("t1"));
        assertTrue(transitionNames.contains("t2"));
    }

    @Test
    public void testSignatures() throws Exception {
        String dashModel = " sig Patient {} sig Medication {}";

        DashModule dashModule = DashUtil.parseEverything_fromStringDash(A4Reporter.NOP, dashModel);
        DashToCoreDash.transformToCoreDash(dashModule);

        DashPythonTranslation translation = new DashPythonTranslation(dashModule);

        System.out.println(translation.basicSigLabels);
        assertEquals(2, translation.basicSigLabels.size());
        assertTrue(translation.basicSigLabels.contains("Patient"));
        assertTrue(translation.basicSigLabels.contains("Medication"));
    }
}
