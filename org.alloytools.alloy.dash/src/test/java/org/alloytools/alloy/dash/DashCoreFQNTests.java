package org.alloytools.alloy.dash;

import java.util.*;

import org.junit.Test;
import static org.junit.Assert.assertEquals;

import ca.uwaterloo.watform.core.*;

public class DashCoreFQNTests {

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

 
}