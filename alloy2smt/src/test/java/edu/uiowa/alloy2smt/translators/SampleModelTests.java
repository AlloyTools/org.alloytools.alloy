package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.alloy2smt.utils.CommandResult;
import org.junit.Test;
import org.junit.jupiter.api.Disabled;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class SampleModelTests
{

    @Test
    public void dijkstra_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/dijkstra.als", true, 0);
        assertEquals("sat", result.satResult);
    }

    @Test
    public void dijkstra_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/dijkstra.als", true, 1);
        assertEquals("unsat", result.satResult);
    }

    @Test
    public void dijkstra_2() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/dijkstra.als", true, 2);
        assertEquals("unsat", result.satResult);
    }

    @Test
    public void messaging_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/messaging.als", true, 0);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void messaging_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/messaging.als", true, 1);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void opt_spantree_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/opt_spantree.als", true, 0);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void opt_spantree_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/opt_spantree.als", true, 1);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void opt_spantree_2() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/opt_spantree.als", true, 2);

        assertEquals("unsat", result.satResult);
    }


    @Test
    public void peterson_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/peterson.als", true, 0);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void peterson_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/peterson.als", true, 1);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void peterson_2() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/peterson.als", true, 2);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void peterson_3() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/peterson.als", true, 3);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void ringlead_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/ringlead.als", true, 0);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void ringlead_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/ringlead.als", true, 1);

        assertEquals("unsat", result.satResult);
    }


    @Test
    public void ringlead_2() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/ringlead.als", true, 2);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void ringlead_3() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/ringlead.als", true, 3);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void ringlead_4() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/ringlead.als", true, 4);

        assertEquals("unsat", result.satResult);
    }

    @Disabled // Kodkod solver can't solve this example
    @Test
    public void s_ringlead() throws Exception
    {
        CommandResult result= AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/s_ringlead.als", true, 0);
    }

    @Test
    public void stable_mutex_ring_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/stable_mutex_ring.als", true, 0);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void stable_mutex_ring_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/stable_mutex_ring.als", true, 1);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void stable_mutex_ring_2() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/stable_mutex_ring.als", true, 2);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void stable_orient_ring_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/stable_mutex_ring.als", true, 0);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void stable_orient_ring_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/stable_mutex_ring.als", true, 1);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void stable_ringlead_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/stable_ringlead.als", true, 0);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void stable_ringlead_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/stable_ringlead.als", true, 1);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void stable_ringlead_2() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/stable_ringlead.als", true, 2);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void stable_ringlead_3() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/stable_ringlead.als", true, 3);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void stable_ringlead_4() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/stable_ringlead.als", true, 4);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void stable_ringlead_5() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/stable_ringlead.als", true, 5);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void chord_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/chord.als", true, 0);
        assertEquals("unsat", result.satResult);
    }

    @Test
    public void chord_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/chord.als", true, 1);
        assertEquals("unsat", result.satResult);
    }

    @Test
    public void chord_2() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/chord.als", true, 2);
        assertEquals("unsat", result.satResult);
    }

    @Test
    public void chord_3() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/chord.als", true, 3);
        assertEquals("sat", result.satResult);
    }

    @Test
    public void chord_4() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/chord.als", true, 4);
        assertEquals("unsat", result.satResult);
    }

    @Test
    public void chord_5() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/chord.als", true, 5);
        assertEquals("unsat", result.satResult);
    }

    @Test
    public void chord_6() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/chord.als", true, 6);
        assertEquals("unsat", result.satResult);
    }

    @Test
    public void chord_7() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/chord.als", true, 7);
        assertEquals("sat", result.satResult);
    }

    @Test
    public void chord_8() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/chord.als", true, 8);
        assertEquals("sat", result.satResult);
    }

    @Test
    public void chord_9() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/chord.als", true, 9);
        assertEquals("sat", result.satResult);
    }

    @Test
    public void chord_10() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/chord.als", true, 10);
        assertEquals("unsat", result.satResult);
    }

    @Test
    public void chord_11() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/chord.als", true, 11);
        assertEquals("unsat", result.satResult);
    }

    @Test
    public void chord_12() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/chord.als", true, 12);
        assertEquals("sat", result.satResult);
    }

    @Test
    public void chord_13() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/chord.als", true, 13);
        assertEquals("sat", result.satResult);
    }

    @Test
    public void chord_14() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/chord.als", true, 14);
        assertEquals("sat", result.satResult);
    }

    @Test
    public void chord_15() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/chord.als", true, 15);
        assertEquals("unsat", result.satResult);
    }

    @Test
    public void chord_16() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/chord.als", true, 16);
        assertEquals("sat", result.satResult);
    }

    @Test
    public void chord2() throws Exception
    {
        CommandResult result= AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/chord2.als", true, 0);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void chordbugmodel_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/chordbugmodel.als", true, 0);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void chordbugmodel_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/chordbugmodel.als", true, 1);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void chordbugmodel_2() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/chordbugmodel.als", true, 2);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void chordbugmodel_3() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/chordbugmodel.als", true, 3);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void chordbugmodel_4() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/chordbugmodel.als", true, 4);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void chordbugmodel_5() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/chordbugmodel.als", true, 5);

        assertEquals("sat", result.satResult);
    }


    @Test
    public void com_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/com.als", true, 0);
        assertEquals("unsat", result.satResult);
    }

    @Test
    public void com_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/com.als", true, 1);
        assertEquals("unsat", result.satResult);
    }

    @Test
    public void com_2() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/com.als", true, 2);
        assertEquals("unsat", result.satResult);
    }

    @Test
    public void com_3() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/com.als", true, 3);
        assertEquals("unsat", result.satResult);
    }

    @Test
    public void com_4() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/com.als", true, 4);
        assertEquals("unsat", result.satResult);
    }

    @Test
    public void firewire_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/firewire.als", true, 0);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void firewire_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/firewire.als", true, 1);

        assertEquals("sat", result.satResult);
    }
    @Test
    public void firewire_2() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/firewire.als", true, 2);

        assertEquals("unsat", result.satResult);
    }
    @Test
    public void firewire_3() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/firewire.als", true, 3);

        assertEquals("unsat", result.satResult);
    }
    @Test
    public void firewire_4() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/firewire.als", true, 4);

        assertEquals("unsat", result.satResult);
    }
    @Test
    public void firewire_5() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/firewire.als", true, 5);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void firewire_6() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/firewire.als", true, 6);

        assertEquals("sat", result.satResult);
    }

    @Disabled // not supported by kodkod solver
    @Test
    public void ins() throws Exception
    {
        CommandResult result= AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/ins.als", true, 0);
    }

    @Test
    public void handshake_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/puzzles/handshake.als", true, 0);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void handshake_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/puzzles/handshake.als", true, 1);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void handshake_2() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/puzzles/handshake.als", true, 2);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void handshake_3() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/puzzles/handshake.als", true, 3);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void file_system_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFileTimeout(60000, "../org.alloytools.alloy.extra/extra/models/examples/systems/file_system.als", true, 0);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void file_system_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFileTimeout(60000, "../org.alloytools.alloy.extra/extra/models/examples/systems/file_system.als", true, 1);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void javatypes_soundness_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/systems/file_system.als", true, 0);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void javatypes_soundness_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/systems/file_system.als", true, 1);

        assertEquals("unsat", result.satResult);
    }


    @Test
    public void lists_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/systems/lists.als", true, 0);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void lists_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/systems/lists.als", true, 1);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void lists_2() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/systems/lists.als", true, 2);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void lists_3() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/systems/lists.als", true, 3);

        assertEquals("sat", result.satResult);
    }


    @Test
    public void marksweepgc_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/systems/marksweepgc.als", true, 0);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void marksweepgc_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/systems/marksweepgc.als", true, 1);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void marksweepgc_2() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/systems/marksweepgc.als", true, 2);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void views() throws Exception
    {
        CommandResult result= AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/systems/views.als", true, 0);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void CeilingsAndFloors_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/toys/CeilingsAndFloors.als", true, 0);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void CeilingsAndFloors_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/toys/CeilingsAndFloors.als", true, 1);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void CeilingsAndFloors_2() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/toys/CeilingsAndFloors.als", true, 2);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void CeilingsAndFloors_3() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/toys/CeilingsAndFloors.als", true, 3);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void CeilingsAndFloors_4() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/toys/CeilingsAndFloors.als", true, 4);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void numbering_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/toys/numbering.als", true, 0);

        assertEquals("unsat", result.satResult);
    }

    @Test
    public void numbering_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/toys/numbering.als", true, 1);

        assertEquals("sat", result.satResult);
    }

    @Test
    public void farmer_0() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/tutorial/farmer.als", true, 0);
        assertEquals("sat", result.satResult);
    }

    @Test
    public void farmer_1() throws Exception
    {
        CommandResult result = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/tutorial/farmer.als", true, 1);
        assertEquals("unsat", result.satResult);
    }
}
