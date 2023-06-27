package edu.mit.csail.sdg.alloy4whole;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.junit.Test;

import edu.mit.csail.sdg.alloy4whole.FindReplace.ReverseString;


public class FindReplaceTest {

    @Test
    public void test() {
        ReverseString rs = new ReverseString("123456");
        assertEquals(rs.toString(), "654321");
        assertEquals(rs.subSequence(0, 6).toString(), "654321");
        assertEquals(rs.subSequence(0, 2).toString(), "65");
        assertEquals(rs.subSequence(2, 4).toString(), "43");
        assertEquals(rs.subSequence(4, 6).toString(), "21");

        Matcher compile = Pattern.compile("432").matcher(rs);
        assertTrue(compile.find());
        int start = compile.start();
        int end = compile.end();
        assertEquals(start, 2);
        assertEquals(end, 5);

        assertEquals(rs.translate(start), 3);
        assertEquals(rs.translate(end), 0);


    }

}
