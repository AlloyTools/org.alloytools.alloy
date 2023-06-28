package edu.mit.csail.sdg.alloy4;

import static org.assertj.core.api.Assertions.assertThat;

import org.junit.Test;


public class PosTest {

    @Test
    public void test() {
        test("abc def ghi", "def", 4, 7, 1, 5, 1, 7);
        test("\nabc def ghi", "def", 5, 8, 2, 5, 2, 7);
        test("\nabc\ndef ghi", "def", 5, 8, 3, 1, 3, 3);
    }

    @Test
    public void testTab() {
        test("\n\tdef ghi", "def", 2, 5, 2, 5, 2, 7);
        test("\n\n\tdef ghi", "def", 3, 6, 3, 5, 3, 7);
        test("\tdef ghi", "def", 1, 4, 1, 5, 1, 7);
        test(" \tdef ghi", "def", 2, 5, 1, 5, 1, 7);
        test("  \tdef ghi", "def", 3, 6, 1, 5, 1, 7);
        test("   \tdef ghi", "def", 4, 7, 1, 5, 1, 7);
        test("    \tdef ghi", "def", 5, 8, 1, 9, 1, 11);
    }

    @Test
    public void testMulti() {
        test("def \n" //
             + "g\n" //
             + "xkl\n", "\ng\n", 4, 7, 1, 5, 2, 2);
    }

    private void test(String text, String extract, int start, int end, int row, int col, int rowEnd, int colEnd) {
        assertThat(text.substring(start, end)).isEqualTo(extract);
        Pos pos = Pos.toPos(text, start, end, 4);
        assertThat(pos.y).isEqualTo(row);
        assertThat(pos.x).isEqualTo(col);
        assertThat(pos.y2).isEqualTo(rowEnd);
        assertThat(pos.x2).isEqualTo(colEnd);
    }

}
