package org.alloytools.alloy.core;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import edu.mit.csail.sdg.alloy4.Pos;

public class PosTest {

    final static String TEST_TEXT_1 = //
                                    "abc def\n" //
                                     + "ghi jkl\n" //
                                     + "mno pqr";

    @Test
    public void testPos() {
        assertPos(TEST_TEXT_1, 0, 3, 1, 1, 1, 3, "abc");
        assertPos(TEST_TEXT_1, 0, 1000, 1, 1, 3, 8, TEST_TEXT_1);
        assertPos(TEST_TEXT_1 + "\n", 0, 1000, 1, 1, 4, 1, TEST_TEXT_1 + "\n");
        assertPos(TEST_TEXT_1, 16, 1000, 3, 1, 3, 7, "mno pqr");
        assertPos(TEST_TEXT_1 + "\n", 16, 1000, 3, 1, 4, 1, "mno pqr\n");
        assertPos(TEST_TEXT_1, 7, 8, 1, 8, 2, 1, "\ng");
        assertPos(TEST_TEXT_1, 8, 11, 2, 1, 2, 3, "ghi");

    }

    private void assertPos(String text, int start, int end, int row, int col, int row2, int col2, String sub) {
        Pos a = Pos.toPos(text, start, end);
        assertEquals(row, a.y);
        assertEquals(col, a.x);
        assertEquals(row2, a.y2);
        assertEquals(col2, a.x2);
        assertEquals(sub, a.substring(text));

        int[] startEnd = a.toStartEnd(text);
        assertEquals(start, startEnd[0]);
        //assertEquals( Math.min(end, text.length()), startEnd[1]);
    }
}
