package org.alloytools.util.table;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

public class TableTest {

    @Test
    public void testUnfilledTable() {
        Table t = new Table(1, 1, 0);
        assertEquals("" + "┌─┐\n" + "│ │\n" + "└─┘\n" + "", t.toString());

    }

    @Test
    public void testEmptyTable() {
        Table t = new Table(0, 0, 0);
        assertEquals("" + "☒" + "", t.toString());

    }


    @Test
    public void testSimpleTable() {
        Table t = new Table(2, 2, 0);
        t.set(0, 0, "0x0");
        t.set(0, 1, "0x1");
        t.set(1, 0, "1x0");
        t.set(1, 1, "1x1");
        assertEquals("" + "┌───┬───┐\n" + "│0x0│0x1│\n" + "├───┼───┤\n" + "│1x0│1x1│\n" + "└───┴───┘\n" + "", t.toString());
    }

    @Test
    public void testTableWithUnequalColumns() {
        Table t = new Table(2, 2, 0);
        t.set(0, 0, "0x0xxxx");
        t.set(0, 1, "0x1");
        t.set(1, 0, "1x0");
        t.set(1, 1, "1x1yyyyyyyyyyyyyyyyyyy");
        assertEquals("" + "┌───────┬──────────────────────┐\n" + "│0x0xxxx│0x1                   │\n" + "├───────┼──────────────────────┤\n" + "│1x0    │1x1yyyyyyyyyyyyyyyyyyy│\n" + "└───────┴──────────────────────┘\n" + "", t.toString());
    }

    @Test
    public void testTableWithUnequalRows() {
        Table t = new Table(2, 2, 0);
        t.set(0, 0, "0x0\n0x0");
        t.set(0, 1, "0x1");
        t.set(1, 0, "1x0");
        t.set(1, 1, "1x1");
        assertEquals("" + "┌───┬───┐\n" + "│0x0│0x1│\n" + "│0x0│   │\n" + "├───┼───┤\n" + "│1x0│1x1│\n" + "└───┴───┘\n" + "", t.toString());
    }

    @Test
    public void testNestedTable() {
        Table t1 = new Table(2, 2, 0);
        t1.set(0, 0, "0x0/1");
        t1.set(0, 1, "0x1/1");
        t1.set(1, 1, "1x1/1");

        Table t2 = new Table(2, 2, 0);
        t2.set(0, 1, "0x1/2");
        t2.set(1, 0, "1x0/2");
        t2.set(1, 1, "1x1/2");

        Table t3 = new Table(2, 2, 0);
        t3.set(0, 0, "0x0/3");
        t3.set(0, 1, "0x1/3");
        t3.set(1, 0, "1x0/3");
        t3.set(1, 1, "1x1/3");

        t1.set(1, 0, t2);
        t2.set(0, 0, t3);

        assertEquals("" + "┌─────────────────┬─────┐\n" + "│0x0/1            │0x1/1│\n" + "├─────┬─────┬─────┼─────┤\n" + "│0x0/3│0x1/3│0x1/2│1x1/1│\n" + "├─────┼─────┤     │     │\n" + "│1x0/3│1x1/3│     │     │\n" + "├─────┴─────┼─────┤     │\n" + "│1x0/2      │1x1/2│     │\n" + "└───────────┴─────┴─────┘\n" + "", t1.toString());
    }

    @Test
    public void testNestedTableWithTopBold() {
        Table t1 = new Table(2, 2, 0);
        t1.setBold();
        t1.set(0, 0, "0x0/1");
        t1.set(0, 1, "0x1/1");
        t1.set(1, 1, "1x1/1");

        Table t2 = new Table(2, 2, 0);
        t2.set(0, 1, "0x1/2");
        t2.set(1, 0, "1x0/2");
        t2.set(1, 1, "1x1/2");

        Table t3 = new Table(2, 2, 0);
        t3.set(0, 0, "0x0/3");
        t3.set(0, 1, "0x1/3");
        t3.set(1, 0, "1x0/3");
        t3.set(1, 1, "1x1/3");

        t1.set(1, 0, t2);
        t2.set(0, 0, t3);

        assertEquals("" + "┏━━━━━━━━━━━━━━━━━┯━━━━━┓\n" + "┃0x0/1            │0x1/1┃\n" + "┠─────┬─────┬─────┼─────┨\n" + "┃0x0/3│0x1/3│0x1/2│1x1/1┃\n" + "┠─────┼─────┤     │     ┃\n" + "┃1x0/3│1x1/3│     │     ┃\n" + "┠─────┴─────┼─────┤     ┃\n" + "┃1x0/2      │1x1/2│     ┃\n" + "┗━━━━━━━━━━━┷━━━━━┷━━━━━┛\n" + "", t1.toString());
    }
}
