/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.alloy4;

import java.io.IOException;
import java.io.RandomAccessFile;
import java.io.UnsupportedEncodingException;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.zip.Deflater;

/**
 * Mutable; implements a growable array of bytes.
 * <p>
 * This class is more efficient than Java's ByteArrayOutputStream when writing
 * large amount of data, because ByteArrayOutputStream will resize and copy
 * entire existing contents every time the array needs to grow, whereas this
 * class maintains a linked list of arrays (so when capacity is expanded we
 * don't need to copy old data)
 */

public final class ByteBuffer {

    /** The size per chunk. */
    private static final int         SIZE = 65536;

    /**
     * The list of chunks allocated so far; always has at least one chunk; every
     * chunk is always exactly of size SIZE.
     */
    private final LinkedList<byte[]> list = new LinkedList<byte[]>();

    /**
     * The number of bytes stored in the latest chunk; every chunk before that is
     * always fully filled.
     */
    private int                      n    = 0;

    /** Construct an empty byte buffer. */
    public ByteBuffer() {
        list.add(new byte[SIZE]);
    }

    /** Write the given byte into this byte buffer. */
    private ByteBuffer w(int b) {
        if (n == SIZE) {
            list.add(new byte[SIZE]);
            n = 0;
        }
        byte[] array = list.getLast();
        array[n] = (byte) b;
        n++;
        return this;
    }

    /** Write the given array of bytes into this byte buffer. */
    private ByteBuffer write(byte[] b, int offset, int len) {
        if (b == null || len <= 0)
            return this;
        else if (n == SIZE) {
            list.add(new byte[SIZE]);
            n = 0;
        }
        while (true) { // loop invariant: len>0 and SIZE>n
            byte[] array = list.getLast();
            if (len <= (SIZE - n)) {
                System.arraycopy(b, offset, array, n, len);
                n += len;
                return this;
            }
            System.arraycopy(b, offset, array, n, SIZE - n);
            offset += (SIZE - n);
            len -= (SIZE - n);
            n = 0;
            list.add(new byte[SIZE]);
        }
    }

    /**
     * Write the given String into this byte buffer (by converting the String into
     * its UTF-8 representation)
     */
    public ByteBuffer write(String string) {
        if (string.length() == 0)
            return this;
        byte[] b;
        try {
            b = string.getBytes("UTF-8");
        } catch (UnsupportedEncodingException ex) {
            return this;
        } // exception not possible
        return write(b, 0, b.length);
    }

    /**
     * Write the given number into this byte buffer, followed by a space.
     */
    public ByteBuffer writes(long x) {
        return write(Long.toString(x)).w(' ');
    }

    /**
     * Write the given number into this byte buffer (truncated to the range
     * -32767..+32767), followed by a space.
     */
    public strictfp ByteBuffer writes(double x) {
        // These extreme values shouldn't happen, but we want to protect against
        // them
        if (Double.isNaN(x))
            return write("0 ");
        else if (x > 32767)
            return write("32767 ");
        else if (x < -32767)
            return write("-32767 ");
        long num = (long) (x * 1000000);
        if (num >= 32767000000L)
            return write("32767 ");
        else if (num <= (-32767000000L))
            return write("-32767 ");
        // Now, regular doubles... let's allow up to 6 digits after the decimal
        // point
        if (num < 0) {
            w('-');
            num = -num;
        }
        String str = Long.toString(num);
        int len = str.length();
        if (len <= 6) {
            w('.');
            while (len < 6) {
                w('0');
                len++;
            }
            return write(str).w(' ');
        }
        return write(str.substring(0, str.length() - 6)).w('.').write(str.substring(str.length() - 6)).w(' ');
    }

    /**
     * Write the entire content into the given file using Flate compression (see
     * RFC1951) then return the number of bytes written.
     */
    public long dumpFlate(RandomAccessFile os) throws IOException {
        Deflater zip = new Deflater(Deflater.BEST_COMPRESSION);
        byte[] output = new byte[8192];
        Iterator<byte[]> it = list.iterator(); // when null, that means we have
                                              // told the Deflater that no
                                              // more input would be coming
        long ans = 0; // the number of bytes written out so far
        while (true) {
            if (it != null && zip.needsInput() && it.hasNext()) {
                byte[] in = it.next();
                if (in == list.getLast()) {
                    zip.setInput(in, 0, n);
                    it = null;
                    zip.finish();
                } else {
                    zip.setInput(in, 0, SIZE);
                }
            }
            if (it == null && zip.finished())
                break;
            int count = zip.deflate(output);
            if (count > 0) {
                ans = ans + count;
                if (ans < 0)
                    throw new IOException("Data too large to be written to the output file.");
                os.write(output, 0, count);
            }
        }
        return ans;
    }

    /**
     * Write the entire content into the given file as-is, then return the number of
     * bytes written.
     */
    public long dump(RandomAccessFile os) throws IOException {
        if (list.size() >= (Long.MAX_VALUE / SIZE))
            throw new IOException("Data too large to be written to the output file.");
        byte[] last = list.getLast();
        for (byte[] x : list)
            if (x != last)
                os.write(x);
        if (n > 0)
            os.write(last, 0, n);
        return ((long) (list.size() - 1)) * SIZE + n;
    }
}
