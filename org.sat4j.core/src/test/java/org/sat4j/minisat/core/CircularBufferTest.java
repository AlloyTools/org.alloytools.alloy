package org.sat4j.minisat.core;

import static org.junit.Assert.assertEquals;

import org.junit.Before;
import org.junit.Test;

public class CircularBufferTest {

    private CircularBuffer buffer;

    @Before
    public void setUp() throws Exception {
        this.buffer = new CircularBuffer(5);
    }

    @Test
    public void test() {
        assertEquals(0, this.buffer.average());
        this.buffer.push(3);
        assertEquals(3, this.buffer.average());
        this.buffer.push(5);
        assertEquals(4, this.buffer.average());
        this.buffer.push(1);
        assertEquals(3, this.buffer.average());
        this.buffer.push(7);
        assertEquals(4, this.buffer.average());
        this.buffer.push(4);
        assertEquals(4, this.buffer.average());
        this.buffer.push(8);
        assertEquals(5, this.buffer.average());
    }

}
