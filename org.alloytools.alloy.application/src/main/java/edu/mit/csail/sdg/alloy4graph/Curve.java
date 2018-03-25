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

package edu.mit.csail.sdg.alloy4graph;

import java.awt.geom.CubicCurve2D;
import java.util.ArrayList;
import java.util.List;

/**
 * Mutable; represents a connected path.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

final class Curve {

    /** starting position and ending position. */
    public double                          startX, startY, endX, endY;

    /** The list of segments in this curve. */
    public final List<CubicCurve2D.Double> list = new ArrayList<CubicCurve2D.Double>();

    /** Construct a curve starting at the given location. */
    public Curve(double startX, double startY) {
        this.startX = startX;
        this.endX = startX;
        this.startY = startY;
        this.endY = startY;
    }

    /** Make a deep copy of this Curve object. */
    public Curve dup() {
        Curve ans = new Curve(startX, startY);
        ans.endX = endX;
        ans.endY = endY;
        for (CubicCurve2D.Double x : list) {
            CubicCurve2D.Double c = new CubicCurve2D.Double();
            c.setCurve(x);
            ans.list.add(c);
        }
        return ans;
    }

    /**
     * Precondition: this.lastX==next.firstX and this.lastY==next.firstY. Note: the
     * resulting Curve will still share the same CubicCurve2D objects as this and
     * that.
     */
    Curve join(Curve that) {
        Curve ans = new Curve(startX, startY);
        ans.list.addAll(list);
        ans.list.addAll(that.list);
        ans.endX = that.endX;
        ans.endY = that.endY;
        return ans;
    }

    /**
     * Produce a cubic bezier curve representing a straightline segment from (x1,y1)
     * to (x2,y2)
     */
    private static CubicCurve2D.Double makeline(double x1, double y1, double x2, double y2) {
        return new CubicCurve2D.Double(x1, y1, (x2 - x1) * 0.3 + x1, (y2 - y1) * 0.3 + y1, (x2 - x1) * 0.6 + x1, (y2 - y1) * 0.6 + y1, x2, y2);
    }

    /** Add a straightline segment to (ax,ay) */
    public Curve lineTo(double ax, double ay) {
        list.add(makeline(endX, endY, ax, ay));
        this.endX = ax;
        this.endY = ay;
        return this;
    }

    /**
     * Add a cubic bezier segment to (cx,cy) using (ax,ay) and (bx,by) as the two
     * control points.
     */
    public Curve cubicTo(double ax, double ay, double bx, double by, double cx, double cy) {
        list.add(new CubicCurve2D.Double(endX, endY, ax, ay, bx, by, cx, cy));
        this.endX = cx;
        this.endY = cy;
        return this;
    }

    /**
     * Returns true if (x1,y1)..(x2,y2) intersects (x,y3)..(x,y4)
     */
    private static boolean intersects(double x1, double y1, double x2, double y2, double x, double y3, double y4) {
        if (!(y3 < y4)) {
            double tmp = y3;
            y3 = y4;
            y4 = tmp;
        }
        if (!((x1 <= x && x <= x2) || (x2 <= x && x <= x1)))
            return false;
        double m = (y2 - y1) / (x2 - x1);
        double i = (x - x1) * m + y1;
        if ((y3 <= i && i <= y4) || (y4 <= i && i <= y3))
            return true;
        else
            return false;
    }

    void bendUp(double x, double y1, double y2, double gap) {
        for (int i = 0; i < list.size(); i++) {
            CubicCurve2D.Double c = list.get(i);
            if (intersects(c.x1, c.y1, c.x2, c.y2, x, y1, y2)) {
                list.set(i, makeline(c.x1, c.y1, x, y1 - gap));
                list.add(i + 1, makeline(x, y1 - gap, c.x2, c.y2));
                return;
            }
        }
    }

    void bendDown(double x, double y1, double y2, double gap) {
        for (int i = 0; i < list.size(); i++) {
            CubicCurve2D.Double c = list.get(i);
            if (intersects(c.x1, c.y1, c.x2, c.y2, x, y1, y2)) {
                list.set(i, makeline(c.x1, c.y1, x, y2 + gap));
                list.add(i + 1, makeline(x, y2 + gap, c.x2, c.y2));
                return;
            }
        }
    }

    /** Chop the start of this curve. */
    public void chopStart(double t) {
        int n = list.size();
        t = t * n;
        double di = StrictMath.floor(t);
        int i = (int) di;
        //
        if (i < 0)
            return;
        if (i >= n)
            list.clear();
        while (i > 0 && !list.isEmpty()) {
            list.remove(0);
            i--;
        }
        if (list.isEmpty()) {
            list.add(new CubicCurve2D.Double(startX = endX, startY = endY, endX, endY, endX, endY, endX, endY));
            return;
        }
        CubicCurve2D.Double tmp = new CubicCurve2D.Double();
        divide(t - di, list.get(0), new CubicCurve2D.Double(), tmp);
        list.get(0).setCurve(tmp);
        startX = tmp.x1;
        startY = tmp.y1;
    }

    /** Chop the end of this curve. */
    public void chopEnd(double t) {
        int n = list.size();
        t = t * n;
        double di = StrictMath.floor(t);
        int i = (int) di;
        //
        if (i < 0)
            list.clear();
        if (i >= n)
            return;
        while (i + 1 < list.size())
            list.remove(i + 1);
        if (list.isEmpty()) {
            endX = startX;
            endY = startY;
            list.add(new CubicCurve2D.Double(endX, endY, endX, endY, endX, endY, endX, endY));
            return;
        }
        CubicCurve2D.Double tmp = new CubicCurve2D.Double();
        divide(t - di, list.get(i), tmp, new CubicCurve2D.Double());
        list.get(i).setCurve(tmp);
        endX = tmp.x2;
        endY = tmp.y2;
    }

    /**
     * Returns the x position at the given y position, or defaultValue if the line
     * doesn't pass thru the given y position.
     * <p>
     * Precondition: the curve is monotonic in the vertical direction.
     */
    public double getXatY(double y, double startT, double endT, double defaultValue) {
        double a = startT, b = endT, ay = getY(a), by = getY(b);
        if (ay > by) {
            double tmp = ay;
            ay = by;
            by = tmp;
            a = endT;
            b = startT;
        }
        if (!(ay <= y && y <= by))
            return defaultValue;
        while (StrictMath.abs(a - b) > 0.001D) {
            double t = (a + b) / 2, ty = getY(t);
            if (ty == y) {
                a = t;
                break;
            } else if (ty < y) {
                a = t;
            } else {
                b = t;
            }
        }
        return getX(a);
    }

    /** Returns the x position at the given point 0 <= t <= 1 */
    public double getX(double t) {
        int n = list.size();
        t = t * n;
        double di = StrictMath.floor(t);
        int i = (int) di;
        if (i < 0)
            return startX;
        else if (i >= n)
            return endX;
        else
            return getX(list.get(i), t - di);
    }

    /** Returns the y position at the given point 0 <= t <= 1 */
    public double getY(double t) {
        int n = list.size();
        t = t * n;
        double di = StrictMath.floor(t);
        int i = (int) di;
        if (i < 0)
            return startY;
        else if (i >= n)
            return endY;
        else
            return getY(list.get(i), t - di);
    }

    /**
     * Returns the x position of the given segment at the given point 0 <= t <= 1
     */
    private double getX(CubicCurve2D.Double curve, double t) {
        double px = (curve.ctrlx1 - curve.x1) * t + curve.x1, qx = (curve.ctrlx2 - curve.ctrlx1) * t + curve.ctrlx1,
                        rx = (curve.x2 - curve.ctrlx2) * t + curve.ctrlx2;
        double sx = (qx - px) * t + px, tx = (rx - qx) * t + qx;
        return (tx - sx) * t + sx;
    }

    /**
     * Returns the y position of the given segment at the given point 0 <= t <= 1
     */
    private double getY(CubicCurve2D.Double curve, double t) {
        double py = (curve.ctrly1 - curve.y1) * t + curve.y1, qy = (curve.ctrly2 - curve.ctrly1) * t + curve.ctrly1,
                        ry = (curve.y2 - curve.ctrly2) * t + curve.ctrly2;
        double sy = (qy - py) * t + py, ty = (ry - qy) * t + qy;
        return (ty - sy) * t + sy;
    }

    /**
     * Given 0<=t<=1 and an existing curve, divide it into two chunks and store the
     * two chunks into "first" and "second"
     */
    public static void divide(double t, CubicCurve2D.Double curve, CubicCurve2D.Double first, CubicCurve2D.Double second) {
        // This algorithm uses de Casteljau's algorithm for chopping one bezier
        // curve into two bezier curves
        first.x1 = curve.x1;
        second.x2 = curve.x2;
        first.ctrlx1 = (1 - t) * curve.x1 + t * curve.ctrlx1;
        double x = (1 - t) * curve.ctrlx1 + t * curve.ctrlx2;
        second.ctrlx2 = (1 - t) * curve.ctrlx2 + t * curve.x2;
        first.ctrlx2 = (1 - t) * first.ctrlx1 + t * x;
        second.ctrlx1 = (1 - t) * x + t * second.ctrlx2;
        second.x1 = first.x2 = (1 - t) * first.ctrlx2 + t * second.ctrlx1;
        // now that we've computed the x coordinates, we now compute the y
        // coordinates
        first.y1 = curve.y1;
        second.y2 = curve.y2;
        first.ctrly1 = (1 - t) * curve.y1 + t * curve.ctrly1;
        double y = (1 - t) * curve.ctrly1 + t * curve.ctrly2;
        second.ctrly2 = (1 - t) * curve.ctrly2 + t * curve.y2;
        first.ctrly2 = (1 - t) * first.ctrly1 + t * y;
        second.ctrly1 = (1 - t) * y + t * second.ctrly2;
        second.y1 = first.y2 = (1 - t) * first.ctrly2 + t * second.ctrly1;
    }
}
