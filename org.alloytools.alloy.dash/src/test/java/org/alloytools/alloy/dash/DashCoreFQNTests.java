package org.alloytools.alloy.dash;

import java.util.*;

import org.junit.Test;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertThrows;
import static org.junit.Assert.assertTrue;

import edu.mit.csail.sdg.alloy4.ErrorFatal;

import ca.uwaterloo.watform.core.*;

public class DashCoreFQNTests {

    public List<String> ll(String[] k) {
        return Arrays.asList(k);
    }

    @Test 
    public void test1() {
        String k = DashFQN.fqn("Root");
        assertEquals(k, "Root");
    }

    @Test 
    public void test2() {
        String k = DashFQN.fqn("Root/A/B");
        assertEquals(k, "Root/A/B");
    }

    @Test 
    public void test3() {
        String k = DashFQN.fqn("Root/A/B");
        assertEquals(k, "Root/A/B");
    }

    @Test
    public void testFQN1()  {
        String k = DashFQN.longestCommonFQN("Root/A","Root/B");
        assertEquals(k,"Root");
    }

    @Test
    public void testFQN2()  {
        String k = DashFQN.longestCommonFQN("Root/A/Bit","Root/B/Bit");
        assertEquals(k,"Root");
    }

    @Test
    public void testFQN3()  {
        String k = DashFQN.longestCommonFQN("Root/B/Bit","Root/B/Bit");
        assertEquals(k,"Root/B/Bit");
    }

    @Test
    public void getChildOfContextAncesOfDest1() {
       assertEquals(
            DashFQN.getChildOfContextAncesOfDest ("A/B/C", "A/B/C/D/E"),
            "A/B/C/D");
    }
    @Test
    public void getChildOfContextAncesOfDest2() {
       assertEquals(
            DashFQN.getChildOfContextAncesOfDest ("A/B/C", "A/B/C"),
            "A/B/C");
    }
    @Test
    public void getChildOfContextAncesOfDest3() {
        Exception exception = assertThrows(ErrorFatal.class, () -> {
            DashFQN.getChildOfContextAncesOfDest ("A/D/C", "A/B/C");
        });
        String actualMessage = exception.getMessage();
        assertTrue(actualMessage.contains(DashErrors.ancesNotPrefixMsg)); 
    }
    @Test
    public void getChildOfContextAncesOfDest4() {
        Exception exception = assertThrows(ErrorFatal.class, () -> {
            DashFQN.getChildOfContextAncesOfDest ("A/B/C", "A/B");
        });
        String actualMessage = exception.getMessage();
        assertTrue(actualMessage.contains(DashErrors.ancesNotPrefixMsg)); 
    }

    @Test 
    public void allPrefixes1() {
        assertTrue(DashFQN.allPrefixes("A").equals(
            ll(new String[]{
                "A"
            })));
    }
    @Test 
    public void allPrefixes2() {
        assertEquals(DashFQN.allPrefixes("A/B"),
            ll(new String[]{
                "A",
                "A/B"
            }));
    }
    @Test 
    public void allPrefixes3() {
        assertEquals(DashFQN.allPrefixes("A/B/C"),
            ll(new String[]{
                "A",
                "A/B",
                "A/B/C"
            }));
    }

    @Test 
    public void suffix() {
        assert(DashFQN.suffix("A/B/C/x", "C/x"));
        assert(DashFQN.suffix("A/B/C/x", "x"));
        assert(DashFQN.suffix("x","x"));
        assert(!DashFQN.suffix("A/B/xyz", "yz"));
    }

    @Test 
    public void mergeFQN() {
        assertTrue(DashFQN.mergeFQN("A/B", "B/C").equals("A/B/C"));
        assertTrue(DashFQN.mergeFQN("A/B/C", "B/C/D").equals("A/B/C/D"));
        assertTrue(DashFQN.mergeFQN("A/B/C", "B/C/D/E").equals("A/B/C/D/E"));
        assertTrue(DashFQN.mergeFQN("A", "A/C").equals("A/C"));
        assertTrue(DashFQN.mergeFQN("A/C", "A/C").equals("A/C"));

        // non-merges
        assertTrue(DashFQN.mergeFQN("", "B/C").equals(""));
        assertTrue(DashFQN.mergeFQN("A/B", "").equals(""));
        assertTrue(DashFQN.mergeFQN("A/B", "D/C").equals(""));
        assertTrue(DashFQN.mergeFQN("A", "D/C").equals(""));
        assertTrue(DashFQN.mergeFQN("A", "C").equals(""));
    }

    @Test 
    public void commonPrefixLength() {
        assertTrue(DashFQN.commonPrefixLength("A/B","A") == 1);
        assertTrue(DashFQN.commonPrefixLength("","A") == 0);
        assertTrue(DashFQN.commonPrefixLength("A/B","") == 0);
        assertTrue(DashFQN.commonPrefixLength("C/B","A") == 0);
        assertTrue(DashFQN.commonPrefixLength("A/B/C/D","A/B") == 2);
        assertTrue(DashFQN.commonPrefixLength("A/B/C","A/B/C/D/E") == 3);
        assertTrue(DashFQN.commonPrefixLength("C/B","A/D") == 0);
    }
}