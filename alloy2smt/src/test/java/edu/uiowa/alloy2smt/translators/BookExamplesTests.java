package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.Utils;
import org.junit.Test;
import org.junit.jupiter.api.Assertions;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;

public class BookExamplesTests
{
    private Translation getExample(String fileName) throws IOException
    {
        String content = new String(Files.readAllBytes(Paths.get(fileName)));
        Translation translation = Utils.translate(content);
        return translation;
    }

    @Test
    public void addressBook1a() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook1a.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void addressBook1b() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook1b.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void addressBook1c() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook1c.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void addressBook1d() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook1d.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void addressBook1e() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook1e.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void addressBook1f() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook1f.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void addressBook1g() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook1g.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void addressBook1h() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook1h.als");
        translation.translateAllCommandsWithCheckSat();
    }


    @Test
    public void addressBook2a() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook2a.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void addressBook2b() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook2b.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void addressBook2c() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook2c.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void addressBook2d() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook2d.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void addressBook2e() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook2e.als");
        translation.translateAllCommandsWithCheckSat();
    }


    @Test
    public void addressBook3a() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook3a.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void addressBook3b() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook3b.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void addressBook3c() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook3c.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void addressBook3d() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter2/addressBook3d.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void filesystem() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter4/filesystem.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void grandpa1() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter4/grandpa1.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void grandpa2() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter4/grandpa2.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void grandpa3() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter4/grandpa3.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void lights() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter4/lights.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void addressBook() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter5/addressBook.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void lists() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter5/lists.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void sets1() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter5/sets1.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void sets2() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter5/sets2.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void hotel1() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter6/hotel1.als");
        translation.translateAllCommandsWithCheckSat();
    }
    @Test
    public void hotel2() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter6/hotel2.als");
        translation.translateAllCommandsWithCheckSat();
    }
    @Test
    public void hotel3() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter6/hotel3.als");
        translation.translateAllCommandsWithCheckSat();
    }
    @Test
    public void hotel4() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter6/hotel4.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void mediaAssets() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter6/mediaAssets.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void ringElection1() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter6/ringElection1.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void ringElection2() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/chapter6/ringElection2.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void addressBook1() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/appendixA/addressBook1.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void addressBook2() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/appendixA/addressBook2.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void barbers() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/appendixA/barbers.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void closure() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/appendixA/closure.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void distribution() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/appendixA/distribution.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void phones() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/appendixA/phones.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void prison() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/appendixA/prison.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void properties() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/appendixA/properties.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void ring() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/appendixA/ring.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void spanning() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/appendixA/spanning.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void tree() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/appendixA/tree.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void tube() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/appendixA/tube.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void undirected() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/appendixA/undirected.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void p300_hotel() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/appendixE/p300-hotel.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void p303_hotel() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/appendixE/p303-hotel.als");
        translation.translateAllCommandsWithCheckSat();
    }

    @Test
    public void p306_hotel() throws IOException
    {
        Translation translation = getExample("../org.alloytools.alloy.extra/extra/models/book/appendixE/p306-hotel.als");
        translation.translateAllCommandsWithCheckSat();
    }
}
