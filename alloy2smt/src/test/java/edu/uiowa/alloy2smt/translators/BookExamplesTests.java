package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.alloy2smt.utils.CommandResult;
import org.junit.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class BookExamplesTests
{
    
    @Test
    public void addressBook1a() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook1a.als", true);
        assertEquals("sat", results.get(0).satResult);
    }

    @Test
    public void addressBook1b() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook1b.als", true);
        assertEquals("sat", results.get(0).satResult);
    }

    @Test
    public void addressBook1c() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook1c.als", true);
        assertEquals("unsat", results.get(0).satResult);
    }

    @Test
    public void addressBook1d() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook1d.als", true);
        assertEquals("sat", results.get(0).satResult);
    }

    @Test
    public void addressBook1e() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook1e.als", true);
        assertEquals("sat", results.get(0).satResult);
    }

    @Test
    public void addressBook1f() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook1f.als", true);
        assertEquals("sat", results.get(0).satResult);
    }

    @Test
    public void addressBook1g() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook1g.als", true);
        assertEquals("sat", results.get(0).satResult);
    }

    @Test
    public void addressBook1h() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook1h.als", true);
        assertEquals("sat", results.get(0).satResult);
        assertEquals("sat", results.get(1).satResult);
        assertEquals("unsat", results.get(2).satResult);
        assertEquals("unsat", results.get(3).satResult);
        assertEquals("unsat", results.get(4).satResult);
        assertEquals("unsat", results.get(5).satResult);
    }


    @Test
    public void addressBook2a() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook2a.als", true);
        assertEquals("sat", results.get(0).satResult);
    }

    @Test
    public void addressBook2b() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook2b.als", true);
        assertEquals("sat", results.get(0).satResult);
    }

    @Test
    public void addressBook2c() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook2c.als", true);
        assertEquals("sat", results.get(0).satResult);
    }

    @Test
    public void addressBook2d() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook2d.als", true);
        assertEquals("sat", results.get(0).satResult);
    }

    @Test
    public void addressBook2e() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook2e.als", true);
        assertEquals("unsat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
        assertEquals("sat", results.get(2).satResult);
        assertEquals("sat", results.get(3).satResult);
    }


    @Test
    public void addressBook3a() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook3a.als", true);
        assertEquals("sat", results.get(0).satResult);
    }

    @Test
    public void addressBook3b() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook3b.als", true);
        assertEquals("unsat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
        assertEquals("unsat", results.get(2).satResult);
        assertEquals("sat", results.get(3).satResult);
    }

    @Test
    public void addressBook3c() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook3c.als", true);
        assertEquals("unsat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
        assertEquals("unsat", results.get(2).satResult);
        assertEquals("sat", results.get(3).satResult);
    }

    @Test
    public void addressBook3d() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook3d.als", true);
        assertEquals("unsat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
        assertEquals("unsat", results.get(2).satResult);
        assertEquals("unsat", results.get(3).satResult);
        assertEquals("unsat", results.get(4).satResult);
    }

    @Test
    public void filesystem() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter4/filesystem.als", true);
        assertEquals("unsat", results.get(0).satResult);
        assertEquals("sat", results.get(1).satResult);
        assertEquals("unsat", results.get(2).satResult);
    }

    @Test
    public void grandpa1() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter4/grandpa1.als", true);
        assertEquals("unsat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
        assertEquals("unsat", results.get(2).satResult);
    }

    @Test
    public void grandpa2() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter4/grandpa2.als", true);
        assertEquals("unsat", results.get(0).satResult);
        assertEquals("sat", results.get(1).satResult);
    }

    @Test
    public void grandpa3() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter4/grandpa3.als", true);
        assertEquals("unsat", results.get(0).satResult);
        assertEquals("sat", results.get(1).satResult);
        assertEquals("unsat", results.get(2).satResult);
    }

    @Test
    public void lights() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter4/lights.als", true);
        assertEquals("unsat", results.get(0).satResult);
    }

    @Test
    public void addressBook() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter5/addressBook.als", true);
        assertEquals("sat", results.get(0).satResult);
        assertEquals("sat", results.get(1).satResult);
    }

    @Test
    public void lists() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter5/lists.als", true);
        assertEquals("unsat", results.get(0).satResult);
    }

    @Test
    public void sets1() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter5/sets1.als", true);
        assertEquals("sat", results.get(0).satResult);
    }

    @Test
    public void sets2() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter5/sets2.als", true);
        assertEquals("unsat", results.get(0).satResult);
    }

    @Test
    public void hotel1() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter6/hotel1.als", true);
        assertEquals("sat", results.get(0).satResult);
    }
    @Test
    public void hotel2() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter6/hotel2.als", true);
        assertEquals("unsat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
        assertEquals("unsat", results.get(2).satResult);
    }
    @Test
    public void hotel3() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter6/hotel3.als", true);

        assertEquals("sat", results.get(0).satResult);
        
    }
    @Test
    public void hotel4() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter6/hotel4.als", true);

        assertEquals("unsat", results.get(0).satResult);
    }

    @Test
    public void mediaAssets() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter6/mediaAssets.als", true);
        assertEquals("unsat", results.get(0).satResult);
        assertEquals("sat", results.get(1).satResult);
        assertEquals("sat", results.get(2).satResult);
        assertEquals("unsat", results.get(3).satResult);
    }

    @Test
    public void ringElection1() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter6/ringElection1.als", true);
        assertEquals("sat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
        assertEquals("sat", results.get(2).satResult);
    }

    @Test
    public void ringElection2() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/chapter6/ringElection2.als", true);

        assertEquals("sat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
        assertEquals("unsat", results.get(2).satResult);
        assertEquals("sat", results.get(3).satResult);
        assertEquals("unsat", results.get(4).satResult);
    }

    @Test
    public void addressBook1() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/appendixA/addressBook1.als", true);
        assertEquals("sat", results.get(0).satResult);
    }

    @Test
    public void addressBook2() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/appendixA/addressBook2.als", true);
        assertEquals("sat", results.get(0).satResult);
    }

    @Test
    public void barbers() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/appendixA/barbers.als", true);
        assertEquals("unsat", results.get(0).satResult);
    }

    @Test
    public void closure() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/appendixA/closure.als", true);
        assertEquals("sat", results.get(0).satResult);
    }

    @Test
    public void distribution() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/appendixA/distribution.als", true);
        assertEquals("unsat", results.get(0).satResult);
    }

    @Test
    public void phones() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/appendixA/phones.als", true);
        assertEquals("sat", results.get(0).satResult);
    }

    @Test
    public void prison() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/appendixA/prison.als", true);
        assertEquals("sat", results.get(0).satResult);
    }

    @Test
    public void properties() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/appendixA/properties.als", true);
        assertEquals("unsat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
    }

    @Test
    public void ring() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/appendixA/ring.als", true);
        assertEquals("sat", results.get(0).satResult);
    }

    @Test
    public void spanning() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/appendixA/spanning.als", true);
        assertEquals("sat", results.get(0).satResult);
    }

    @Test
    public void tree() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/appendixA/tree.als", true);
        assertEquals("sat", results.get(0).satResult);
    }

    @Test
    public void tube() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/appendixA/tube.als", true);
        assertEquals("sat", results.get(0).satResult);
    }

    @Test
    public void undirected() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/appendixA/undirected.als", true);
        assertEquals("sat", results.get(0).satResult);
    }

    @Test
    public void p300_hotel() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/appendixE/p300-hotel.als", true);
        assertEquals("sat", results.get(0).satResult);
    }

    @Test
    public void p303_hotel() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/appendixE/p303-hotel.als", true);
        assertEquals("unsat", results.get(0).satResult);
        assertEquals("sat", results.get(1).satResult);
    }

    @Test
    public void p306_hotel() throws Exception
    {
        List<CommandResult> results = AlloyUtils.runAlloyFile("../org.alloytools.alloy.extra/extra/models/book/appendixE/p306-hotel.als", true);
        assertEquals("unsat", results.get(0).satResult);
        assertEquals("unsat", results.get(1).satResult);
        assertEquals("unsat", results.get(2).satResult);

    }
}
