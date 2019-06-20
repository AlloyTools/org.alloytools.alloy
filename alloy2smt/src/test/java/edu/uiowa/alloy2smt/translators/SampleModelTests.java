package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.Utils;
import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.alloy2smt.utils.CommandResult;
import org.junit.Test;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Disabled;

import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class SampleModelTests
{

    @Test
    public void dijkstra() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/dijkstra.als", true);
        assertEquals("sat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
        assertEquals("unsat", results.get(2).satResult);
    }

    @Test
    public void messaging() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/messaging.als", true);

        assertEquals("sat", results.get(0).satResult);
        assertEquals("sat", results.get(1).satResult);
    }

    @Test
    public void opt_spantree() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/opt_spantree.als", true);

        assertEquals("sat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
        assertEquals("unsat", results.get(2).satResult);
    }

    @Test
    public void peterson() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/peterson.als", true);

        assertEquals("unsat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
        assertEquals("unsat", results.get(2).satResult);
        assertEquals("unsat", results.get(3).satResult);
    }

    @Test
    public void ringlead() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/ringlead.als", true);

        assertEquals("sat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
        assertEquals("unsat", results.get(2).satResult);
        assertEquals("sat", results.get(3).satResult);
        assertEquals("unsat", results.get(4).satResult);
    }

    @Disabled // Kodkod solver can't solve this example
    @Test
    public void s_ringlead() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/s_ringlead.als", true);
    }

    @Test
    public void stable_mutex_ring() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/stable_mutex_ring.als", true);

        assertEquals("sat", results.get(0).satResult);
        assertEquals("sat", results.get(1).satResult);
        assertEquals("unsat", results.get(2).satResult);
    }

    @Test
    public void stable_orient_ring() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/stable_mutex_ring.als", true);

        assertEquals("sat", results.get(0).satResult);
        assertEquals("sat", results.get(1).satResult);
    }

    @Test
    public void stable_ringlead() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/algorithms/stable_ringlead.als", true);

        assertEquals("sat", results.get(0).satResult);
        assertEquals("sat", results.get(1).satResult);
        assertEquals("sat", results.get(2).satResult);
        assertEquals("unsat", results.get(3).satResult);
        assertEquals("sat", results.get(4).satResult);
        assertEquals("unsat", results.get(5).satResult);
    }

    @Test
    public void chord() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/chord.als", true);

        assertEquals("unsat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
        assertEquals("unsat", results.get(2).satResult);
        assertEquals("sat", results.get(3).satResult);
        assertEquals("unsat", results.get(4).satResult);

        assertEquals("unsat", results.get(5).satResult);
        assertEquals("unsat", results.get(6).satResult);
        assertEquals("sat", results.get(7).satResult);
        assertEquals("sat", results.get(8).satResult);
        assertEquals("sat", results.get(9).satResult);

        assertEquals("unsat", results.get(10).satResult);
        assertEquals("unsat", results.get(11).satResult);
        assertEquals("sat", results.get(12).satResult);
        assertEquals("sat", results.get(13).satResult);
        assertEquals("sat", results.get(14).satResult);

        assertEquals("unsat", results.get(15).satResult);
        assertEquals("sat", results.get(16).satResult);
    }

    @Test
    public void chord2() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/chord2.als", true);

        assertEquals("unsat", results.get(0).satResult);
    }

    @Test
    public void chordbugmodel() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/chordbugmodel.als", true);

        assertEquals("sat", results.get(0).satResult);
        assertEquals("sat", results.get(1).satResult);
        assertEquals("sat", results.get(2).satResult);
        assertEquals("sat", results.get(3).satResult);
        assertEquals("unsat", results.get(4).satResult);
        assertEquals("sat", results.get(5).satResult);
    }

    @Test
    public void com() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/com.als", true);

        assertEquals("unsat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
        assertEquals("unsat", results.get(2).satResult);
        assertEquals("unsat", results.get(3).satResult);
        assertEquals("unsat", results.get(4).satResult);
    }

    @Test
    public void firewire() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/firewire.als", true);

        assertEquals("sat", results.get(0).satResult);
        assertEquals("sat", results.get(1).satResult);
        assertEquals("unsat", results.get(2).satResult);
        assertEquals("unsat", results.get(3).satResult);
        assertEquals("unsat", results.get(4).satResult);
        assertEquals("unsat", results.get(5).satResult);
        assertEquals("sat", results.get(6).satResult);
    }

    @Disabled // not supported by kodkod solver
    @Test
    public void ins() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/case_studies/ins.als", true);
    }

    @Test
    public void handshake() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/puzzles/handshake.als", true);

        assertEquals("sat", results.get(0).satResult);
        assertEquals("sat", results.get(1).satResult);
        assertEquals("sat", results.get(2).satResult);
        assertEquals("sat", results.get(3).satResult);
    }

    @Test
    public void file_system() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/systems/file_system.als", true, 60000);

        assertEquals("sat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
    }

    @Test
    public void javatypes_soundness() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/systems/file_system.als", true);

        assertEquals("unsat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
    }

    @Test
    public void lists() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/systems/lists.als", true);

        assertEquals("unsat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
        assertEquals("unsat", results.get(2).satResult);
        assertEquals("sat", results.get(3).satResult);
    }

    @Test
    public void marksweepgc() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/systems/marksweepgc.als", true);

        assertEquals("unsat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
        assertEquals("unsat", results.get(2).satResult);
    }

    @Test
    public void views() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/systems/views.als", true);

        assertEquals("sat", results.get(0).satResult);
    }

    @Test
    public void CeilingsAndFloors() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/toys/CeilingsAndFloors.als", true);

        assertEquals("sat", results.get(0).satResult);
        assertEquals("unsat", results.get(0).satResult);
        assertEquals("sat", results.get(2).satResult);
        assertEquals("unsat", results.get(3).satResult);
        assertEquals("unsat", results.get(4).satResult);
    }

    @Test
    public void numbering() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/toys/numbering.als", true);

        assertEquals("unsat", results.get(0).satResult);
        assertEquals("sat", results.get(0).satResult);
    }

    @Test
    public void farmer() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/examples/tutorial/farmer.als", true);
        assertEquals("sat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
    }
}
