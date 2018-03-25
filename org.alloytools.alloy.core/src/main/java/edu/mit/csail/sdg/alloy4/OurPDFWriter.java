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

import java.awt.Color;
import java.awt.Polygon;
import java.awt.Shape;
import java.awt.geom.PathIterator;
import java.io.IOException;
import java.io.RandomAccessFile;

/**
 * Graphical convenience methods for producing PDF files.
 * <p>
 * This implementation explicitly generates a very simple 8.5 inch by 11 inch
 * one-page PDF consisting of graphical operations. Hopefully this class will no
 * longer be needed in the future once Java comes with better PDF support.
 */

public final strictfp class OurPDFWriter {

    /** The filename. */
    private final String filename;

    /** The page width (in terms of dots). */
    private final long   width;

    /** The page height (in terms of dots). */
    private final long   height;

    /**
     * Latest color expressed as RGB (-1 if none has been explicitly set so far)
     */
    private int          color = -1;

    /**
     * Latest line style (0=normal, 1=bold, 2=dotted, 3=dashed)
     */
    private int          line  = 0;

    /**
     * The buffer that will store the list of graphical operations issued so far
     * (null if close() has been called successfully)
     */
    private ByteBuffer   buf   = new ByteBuffer();

    /**
     * Begin a blank PDF file with the given dots-per-inch and the given scale (the
     * given file, if existed, will be overwritten)
     *
     * @throws IllegalArgumentException if dpi is less than 50 or is greater than
     *             3000
     */
    public OurPDFWriter(String filename, int dpi, double scale) {
        if (dpi < 50 || dpi > 3000)
            throw new IllegalArgumentException("The DPI must be between 50 and 3000");
        this.filename = filename;
        width = dpi * 8L + (dpi / 2L); // "8.5 inches"
        height = dpi * 11L; // "11 inches"
        // Write the default settings, and flip (0, 0) into the top-left corner
        // of the page, scale the page, then leave 0.5" margin
        buf.write("q\n" + "1 J\n" + "1 j\n" + "[] 0 d\n" + "1 w\n" + "1 0 0 -1 0 ").writes(height).write("cm\n");
        buf.writes(scale).write("0 0 ").writes(scale).writes(dpi / 2.0).writes(dpi / 2.0).write("cm\n");
        buf.write("1 0 0 1 ").writes(dpi / 2.0).writes(dpi / 2.0).write("cm\n");
    }

    /** Changes the color for subsequent graphical drawing. */
    public OurPDFWriter setColor(Color color) {
        int rgb = color.getRGB() & 0xFFFFFF, r = (rgb >> 16), g = (rgb >> 8) & 0xFF, b = (rgb & 0xFF);
        if (this.color == rgb)
            return this;
        else
            this.color = rgb; // no need to change
        buf.writes(r / 255.0).writes(g / 255.0).writes(b / 255.0).write("RG\n");
        buf.writes(r / 255.0).writes(g / 255.0).writes(b / 255.0).write("rg\n");
        return this;
    }

    /** Changes the line style to be normal. */
    public OurPDFWriter setNormalLine() {
        if (line != 0)
            buf.write("1 w [] 0 d\n");
        line = 0;
        return this;
    }

    /** Changes the line style to be bold. */
    public OurPDFWriter setBoldLine() {
        if (line != 1)
            buf.write("2 w [] 0 d\n");
        line = 1;
        return this;
    }

    /** Changes the line style to be dotted. */
    public OurPDFWriter setDottedLine() {
        if (line != 2)
            buf.write("1 w [1 3] 0 d\n");
        line = 2;
        return this;
    }

    /** Changes the line style to be dashed. */
    public OurPDFWriter setDashedLine() {
        if (line != 3)
            buf.write("1 w [6 3] 0 d\n");
        line = 3;
        return this;
    }

    /** Shifts the coordinate space by the given amount. */
    public OurPDFWriter shiftCoordinateSpace(int x, int y) {
        buf.write("1 0 0 1 ").writes(x).writes(y).write("cm\n");
        return this;
    }

    /** Draws a line from (x1, y1) to (x2, y2). */
    public OurPDFWriter drawLine(int x1, int y1, int x2, int y2) {
        buf.writes(x1).writes(y1).write("m ").writes(x2).writes(y2).write("l S\n");
        return this;
    }

    /**
     * Draws a circle of the given radius, centered at (0, 0).
     */
    public OurPDFWriter drawCircle(int radius, boolean fillOrNot) {
        double k = (0.55238 * radius); // Approximate a circle using 4 cubic
                                      // bezier curves
        buf.writes(radius).write("0 m ");
        buf.writes(radius).writes(k).writes(k).writes(radius).write("0 ").writes(radius).write("c ");
        buf.writes(-k).writes(radius).writes(-radius).writes(k).writes(-radius).write("0 c ");
        buf.writes(-radius).writes(-k).writes(-k).writes(-radius).write("0 ").writes(-radius).write("c ");
        buf.writes(k).writes(-radius).writes(radius).writes(-k).writes(radius).write(fillOrNot ? "0 c f\n" : "0 c S\n");
        return this;
    }

    /** Draws a shape. */
    public OurPDFWriter drawShape(Shape shape, boolean fillOrNot) {
        if (shape instanceof Polygon) {
            Polygon obj = (Polygon) shape;
            for (int i = 0; i < obj.npoints; i++)
                buf.writes(obj.xpoints[i]).writes(obj.ypoints[i]).write(i == 0 ? "m\n" : "l\n");
            buf.write("h\n");
        } else {
            double moveX = 0, moveY = 0, nowX = 0, nowY = 0, pt[] = new double[6];
            for (PathIterator it = shape.getPathIterator(null); !it.isDone(); it.next())
                switch (it.currentSegment(pt)) {
                    case PathIterator.SEG_MOVETO :
                        nowX = moveX = pt[0];
                        nowY = moveY = pt[1];
                        buf.writes(nowX).writes(nowY).write("m\n");
                        break;
                    case PathIterator.SEG_CLOSE :
                        nowX = moveX;
                        nowY = moveY;
                        buf.write("h\n");
                        break;
                    case PathIterator.SEG_LINETO :
                        nowX = pt[0];
                        nowY = pt[1];
                        buf.writes(nowX).writes(nowY).write("l\n");
                        break;
                    case PathIterator.SEG_CUBICTO :
                        nowX = pt[4];
                        nowY = pt[5];
                        buf.writes(pt[0]).writes(pt[1]).writes(pt[2]).writes(pt[3]).writes(nowX).writes(nowY).write("c\n");
                        break;
                    case PathIterator.SEG_QUADTO : // Convert quadratic bezier
                                                  // into cubic bezier using
                                                  // de Casteljau algorithm
                        double px = nowX + (pt[0] - nowX) * (2.0 / 3.0), qx = px + (pt[2] - nowX) / 3.0;
                        double py = nowY + (pt[1] - nowY) * (2.0 / 3.0), qy = py + (pt[3] - nowY) / 3.0;
                        nowX = pt[2];
                        nowY = pt[3];
                        buf.writes(px).writes(py).writes(qx).writes(qy).writes(nowX).writes(nowY).write("c\n");
                        break;
                }
        }
        buf.write(fillOrNot ? "f\n" : "S\n");
        return this;
    }

    /*
     * PDF File Structure Summary: =========================== File should ideally
     * start with the following 13 bytes: "%PDF-1.3" 10 "%" -127 10 10 Now comes one
     * or more objects. One simple single-page arrangement is to have exactly 5
     * objects in this order: FONT, CONTENT, PAGE, PAGES, and CATALOG. Font Object
     * (1 because FONT is #1) ================================== 1 0 obj << /Type
     * /Font /Subtype /Type1 /BaseFont /Helvetica /Encoding /WinAnsiEncoding >>
     * endobj\n\n Content Object (2 because CONTENT is #2) (${LEN} is the number of
     * bytes in ${CONTENT} when compressed)
     * ========================================================= ================
     * ============================= 2 0 obj << /Length ${LEN} /Filter /FlateDecode
     * >> stream\r\n${CONTENT}endstream endobj\n\n Here is a quick summary of
     * various PDF Graphics operations
     * ========================================================= = $x $y m -->
     * begins a new path at the given coordinate $x $y l --> add the segment
     * (LASTx,LASTy)..($x,$y) to the current path $cx $cy $x $y v --> add the bezier
     * curve (LASTx,LASTy)..(LASTx,LASTy)..($cx,$cy)..($x,$y) to the current path
     * $cx $cy $x $y y --> add the bezier curve
     * (LASTx,LASTy)....($cx,$cy).....($x,$y)...($x,$y) to the current path $ax $ay
     * $bx $by $x $y c --> add the bezier curve
     * (LASTx,LASTy)....($ax,$ay)....($bx,$by)..($x,$y) to the current path h -->
     * close the current subpath by straightline segment from current point to the
     * start of this subpath $x $y $w $h re --> append a rectangle to the current
     * path as a complete subpath with lower-left corner at $x $y S --> assuming
     * we've just described a path, draw the path f --> assuming we've just
     * described a path, fill the path B --> assuming we've just described a path,
     * fill then draw the path q --> saves the current graphics state 1 J --> sets
     * the round cap 1 j --> sets the round joint [] 0 d --> sets the dash pattern
     * as SOLID [4 6] 0 d --> sets the dash pattern as 4 UNITS ON then 6 UNITS OFF 5
     * w --> sets the line width as 5 UNITS $a $b $c $d $e $f cm --> appends the
     * given matrix; for example, [1 0 0 1 dx dy] means "translation to dx dy" $R $G
     * $B RG --> sets the stroke color (where 0 <= $R <= 1, etc) $R $G $B rg -->
     * sets the fill color (where 0 <= $R <= 1, etc) Q --> restores the current
     * graphics state Page Object (3 because PAGE is #3) (4 beacuse PAGES is #4) (2
     * because CONTENTS is #2)
     * ========================================================= ================
     * ============ 3 0 obj << /Type /Page /Parent 4 0 R /Contents 2 0 R >>
     * endobj\n\n Pages Object (4 because PAGES is #4) (3 because PAGE is #3) (${W}
     * is 8.5*DPI, ${H} is 11*DPI) (1 because FONT is #1)
     * ========================================================= ================
     * =========================================== 4 0 obj << /Type /Pages /Count 1
     * /Kids [3 0 R] /MediaBox [0 0 ${W} ${H}] /Resources << /Font << /F1 1 0 R >>
     * >> >> endobj\n\n Catalog Object (5 because CATALOG is #5) (4 because PAGES is
     * #4) ========================================================= ======= 5 0 obj
     * << /Type /Catalog /Pages 4 0 R >> endobj\n\n END_OF_FILE format (assuming we
     * have obj1 obj2 obj3 obj4 obj5 where obj5 is the "PDF Catalog")
     * ========================================================= ================
     * ===================== xref\n 0 6\n // 6 is because it's the number of objects
     * plus 1 0000000000 65535 f\r\n ${offset1} 00000 n\r\n // ${offset1} is byte
     * offset of start of obj1, left-padded-with-zero until you get exactly 10
     * digits ${offset2} 00000 n\r\n // ${offset2} is byte offset of start of obj2,
     * left-padded-with-zero until you get exactly 10 digits ${offset3} 00000 n\r\n
     * // ${offset3} is byte offset of start of obj3, left-padded-with-zero until
     * you get exactly 10 digits ${offset4} 00000 n\r\n // ${offset4} is byte offset
     * of start of obj4, left-padded-with-zero until you get exactly 10 digits
     * ${offset5} 00000 n\r\n // ${offset5} is byte offset of start of obj5,
     * left-padded-with-zero until you get exactly 10 digits trailer\n <<\n /Size
     * 6\n // 6 is because it's the number of objects plus 1 /Root 5 0 R\n // 5 is
     * because it's the Catalog Object's object ID >>\n startxref\n ${xref}\n //
     * $xref is the byte offset of the start of this entire "xref" paragraph %%EOF\n
     */

    /**
     * Helper method that writes the given String to the output file, then return
     * the number of bytes written.
     */
    private static int out(RandomAccessFile file, String string) throws IOException {
        byte[] array = string.getBytes("UTF-8");
        file.write(array);
        return array.length;
    }

    /** Close and save this PDF object. */
    public void close() throws IOException {
        if (buf == null)
            return; // already closed
        final boolean compressOrNot = true;
        RandomAccessFile out = null;
        try {
            String space = "                    "; // reserve 20 bytes for the
                                                  // file size, which is far
                                                  // far more than enough
            final long fontID = 1, contentID = 2, pageID = 3, pagesID = 4, catalogID = 5, offset[] = new long[6];
            // Write %PDF-1.3, followed by a non-ASCII comment to force the PDF
            // into binary mode
            out = new RandomAccessFile(filename, "rw");
            out.setLength(0);
            byte[] head = new byte[] {
                                      '%', 'P', 'D', 'F', '-', '1', '.', '3', 10, '%', -127, 10, 10
            };
            out.write(head);
            long now = head.length;
            // Font
            offset[1] = now;
            now += out(out, fontID + " 0 obj << /Type /Font /Subtype /Type1 /BaseFont" + " /Helvetica /Encoding /WinAnsiEncoding >> endobj\n\n");
            // Content
            offset[2] = now;
            now += out(out, contentID + " 0 obj << /Length " + space + (compressOrNot ? " /Filter /FlateDecode" : "") + " >> stream\r\n");
            buf.write("Q\n");
            final long ct = compressOrNot ? buf.dumpFlate(out) : buf.dump(out);
            now += ct + out(out, "endstream endobj\n\n");
            // Page
            offset[3] = now;
            now += out(out, pageID + " 0 obj << /Type /Page /Parent " + pagesID + " 0 R /Contents " + contentID + " 0 R >> endobj\n\n");
            // Pages
            offset[4] = now;
            now += out(out, pagesID + " 0 obj << /Type /Pages /Count 1 /Kids [" + pageID + " 0 R] /MediaBox [0 0 " + width + " " + height + "] /Resources << /Font << /F1 " + fontID + " 0 R >> >> >> endobj\n\n");
            // Catalog
            offset[5] = now;
            now += out(out, catalogID + " 0 obj << /Type /Catalog /Pages " + pagesID + " 0 R >> endobj\n\n");
            // Xref
            String xr = "xref\n" + "0 " + offset.length + "\n";
            for (int i = 0; i < offset.length; i++) {
                String txt = Long.toString(offset[i]);
                while (txt.length() < 10)
                    txt = "0" + txt; // must be exactly 10 characters long
                if (i == 0)
                    xr = xr + txt + " 65535 f\r\n";
                else
                    xr = xr + txt + " 00000 n\r\n";
            }
            // Trailer
            xr = xr + "trailer\n<<\n/Size " + offset.length + "\n/Root " + catalogID + " 0 R\n>>\n" + "startxref\n" + now + "\n%%EOF\n";
            out(out, xr);
            out.seek(offset[2]);
            out(out, contentID + " 0 obj << /Length " + ct); // move the file
                                                            // pointer back
                                                            // so we can
                                                            // write out the
                                                            // real Content
                                                            // Size
            out.close();
            buf = null; // only set buf to null if the file was saved
                       // successfully and no exception was thrown
        } catch (Throwable ex) {
            Util.close(out);
            if (ex instanceof IOException)
                throw (IOException) ex;
            if (ex instanceof OutOfMemoryError)
                throw new IOException("Out of memory trying to save the PDF file to " + filename);
            if (ex instanceof StackOverflowError)
                throw new IOException("Out of memory trying to save the PDF file to " + filename);
            throw new IOException("Error writing the PDF file to " + filename + " (" + ex + ")");
        }
    }
}
