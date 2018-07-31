package tests.basic;

import java.util.Iterator;

import junit.framework.TestCase;
import kodkod.util.ints.ArraySequence;
import kodkod.util.ints.IndexedEntry;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.IntTreeSet;
import kodkod.util.ints.Ints;
import kodkod.util.ints.RangeSequence;
import kodkod.util.ints.SparseSequence;
import kodkod.util.ints.TreeSequence;

/**
 * Tests sparse sequence implementation(s).
 *
 * @author Emina Torlak
 */
public class SparseSequenceTest extends TestCase {

    private SparseSequence<Integer> s0;

    @Override
    protected void setUp() throws Exception {
        s0 = new TreeSequence<Integer>();
    }

    public void testPutGetRemoveSize() {
        assertTrue(s0.size() == 0);
        s0.put(0, 0);
        assertTrue(s0.get(0).intValue() == 0);
        assertTrue(s0.size() == 1);
        s0.put(Integer.MIN_VALUE, Integer.MIN_VALUE);
        assertTrue(s0.get(Integer.MIN_VALUE).intValue() == Integer.MIN_VALUE);
        assertTrue(s0.size() == 2);
        s0.put(Integer.MAX_VALUE, Integer.MAX_VALUE);
        assertTrue(s0.get(Integer.MAX_VALUE).intValue() == Integer.MAX_VALUE);
        assertTrue(s0.size() == 3);
        s0.put(2, 0);
        assertTrue(s0.get(0).intValue() == 0);
        assertTrue(s0.size() == 4);
        s0.put(1, 0);
        assertTrue(s0.get(1).intValue() == 0);
        assertTrue(s0.size() == 5);
        s0.put(-1, 0);
        assertTrue(s0.get(-1).intValue() == 0);
        assertTrue(s0.size() == 6);
        s0.put(3, 0);
        assertTrue(s0.get(3).intValue() == 0);
        assertTrue(s0.size() == 7);
        s0.remove(0);
        assertTrue(s0.size() == 6);
        s0.remove(Integer.MIN_VALUE);
        assertTrue(s0.size() == 5);
        s0.remove(3);
        assertTrue(s0.size() == 4);
        s0.put(2, 2);
        assertTrue(s0.get(2).intValue() == 2);
        assertTrue(s0.size() == 4);
        s0.put(0, 2);
        assertTrue(s0.get(0).intValue() == 2);
        assertTrue(s0.size() == 5);
        s0.put(1, 2);
        assertTrue(s0.get(1).intValue() == 2);
        assertTrue(s0.size() == 5);
        // System.out.println(s0);
    }

    public void testIterator() {
        for (int i = 0; i < 10; i++)
            s0.put(i, 0);
        // System.out.println(s0);
        Iterator<IndexedEntry<Integer>> iter = s0.iterator();
        for (int i = 0; i < 10; i++) {
            iter.next();
            // System.out.println(iter.next());
        }
        // if (iter.hasNext())
        // System.out.println(iter.next());
        assertFalse(iter.hasNext());
    }

    public void testRange() {
        s0 = new RangeSequence<Integer>();
        s0.put(16, 0);
        s0.put(17, 0);
        // System.out.println(s0);
        s0.put(16, 1);
        s0.put(17, 2);
        // System.out.println(s0);
    }

    public void testRemove() {
        // [2597 b NIL [2630 r [2616 b [2604 b NIL NIL] [2623 b NIL NIL]]
        // [2658 b [2644 r [2637 b NIL NIL] [2651 b NIL [2655 r NIL NIL]]] [2660
        // b NIL NIL]]]]
        // s0 = new TreeSequence<Integer>();
        // s0.put(2597, 0);
        // s0.put(2630, 0);
        // s0.put(2616, 0);
        // s0.put(2604, 0);
        // s0.put(2623, 0);
        // s0.put(2658, 0);
        // s0.put(2644, 0);
        // s0.put(2637, 0);
        // s0.put(2651, 0);
        // System.out.println(s0);
        // s0.remove(2616);
        // System.out.println(s0);

        // root: [221 b [51 r [45 b NIL NIL] [168 b NIL NIL]] [331 b NIL NIL]]
        // z: [51 b null null]
        // root: [221 b [168 b [45 r NIL NIL] NIL] [331 b NIL NIL]]
        s0.clear();

        s0.put(331, 0);
        s0.put(221, 0);
        s0.put(168, 0);
        // s0.put(48, 0);
        // s0.put(42, 0);
        s0.put(45, 0);
        s0.put(51, 0);

        System.out.println(s0);
        s0.remove(51);
        System.out.println(s0);
    }

    // public void testFirstLast() {
    // for(int i = 0; i < 10; i++)
    // s0.put(i, 0);
    // IndexedEntry<Integer> e0 = s0.first();
    // while (e0 != null) {
    // System.out.println(e0);
    // e0 = s0.successor(e0.index());
    // }
    // }

    public void testClone() {
        final IntSet s = Ints.bestSet(3);
        s.add(1);
        s.add(2);
        s0 = new ArraySequence<Integer>(s);
        s0.put(1, 0);
        s0.put(2, 0);
        try {
            SparseSequence<Integer> s1 = s0.clone();
            assertTrue(s1.equals(s0));
            assertNotSame(s1, s0);
            SparseSequence<Integer> s2 = new ArraySequence<Integer>(s);
            s2.putAll(s0);
            s1.remove(1);
            assertTrue(s2.equals(s0));
            assertFalse(s1.equals(s0));
        } catch (CloneNotSupportedException e) {
            assert false;
        }

    }

    public void testIntTreeSet() {
        IntTreeSet s = new IntTreeSet();
        // s.add(1);
        // System.out.println(s);
        // s.add(3);
        // System.out.println(s);
        // s.add(2);
        // System.out.println(s);
        s.add(331);
        s.add(221);
        for (int i = 42; i <= 45; i++)
            s.add(i);
        for (int i = 47; i <= 51; i++)
            s.add(i);
        s.add(167);
        s.add(168);
        s.add(220);

        System.out.println(s);
        s.add(46);
        System.out.println(s);
    }

}
