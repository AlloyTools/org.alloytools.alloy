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

import java.io.Serializable;

/** Immutable; stores the filename and line/column position.
 *
 * <p> <b>Invariant:</b>     filename!=null && x>0 && y>0 && ((y2>y && x2>0) || (y2==y && x2>=x))
 *
 * <p><b>Thread Safety:</b>  Safe (since objects of this class are immutable).
 */

public final class Pos implements Serializable {

   /** To make sure the serialization form is stable. */
   private static final long serialVersionUID = 0;

   /** The filename (it can be an empty string if unknown) */
   public final String filename;

   /** The starting column position (from 1..) */
   public final int x;

   /** The starting row position (from 1..) */
   public final int y;

   /** The ending column position (from 1..) */
   public final int x2;

   /** The ending row position (from 1..) */
   public final int y2;

   /** The default "unknown" location. */
   public static final Pos UNKNOWN = new Pos("",1,1);

   /** Constructs a new Pos object.
    * @param filename - the filename (it can be an empty string if unknown)
    * @param x - the column position (from 1..)
    * @param y - the row position (from 1..)
    */
   public Pos(String filename, int x, int y) {
      this.filename = (filename==null ? "" : filename);
      this.x = (x>0 ? x : 1);
      this.y = (y>0 ? y : 1);
      this.x2 = this.x;
      this.y2 = this.y;
   }

   /** Constructs a new Pos object.
    * @param filename - the filename (it can be an empty string if unknown)
    * @param x - the starting column position (from 1..)
    * @param y - the starting row position (from 1..)
    * @param x2 - the ending column position (from 1..)
    * @param y2 - the ending row position (from 1..)
    */
   public Pos(String filename, int x, int y, int x2, int y2) {
      this.filename = (filename==null ? "" : filename);
      this.x = (x>0 ? x : 1);
      this.y = (y>0 ? y : 1);
      if (y2<(this.y)) y2=this.y;
      if (y2==this.y) {
         if (x2<(this.x)) x2=this.x;
      } else {
         if (x2<1) x2=1;
      }
      this.x2 = x2;
      this.y2 = y2;
   }

   /** Return a new position that merges this and that (it is assumed that the two Pos objects have same filename)
    * @param that - the other position object
    */
   public Pos merge(Pos that) {
      if (that==null || that==UNKNOWN || that==this) return this;
      if (this==UNKNOWN) return that;
      int x=this.x, y=this.y, x2=that.x2, y2=that.y2;
      if (that.y<y || (that.y==y && that.x<x)) {
         x=that.x;
         y=that.y;
      }
      if (this.y2>y2 || (this.y2==y2 && this.x2>x2)) {
         x2=this.x2;
         y2=this.y2;
      }
      if (x==this.x && y==this.y && x2==this.x2 && y2==this.y2) return this; // avoid creating unnecessary new object
      if (x==that.x && y==that.y && x2==that.x2 && y2==that.y2) return that; // avoid creating unnecessary new object
      return new Pos(filename, x, y, x2, y2);
   }

   /** Returns true if neither argument is null nor UNKNOWN,
    * and that the ending position of "a" is before the starting position of "b".
    */
   public static boolean before(Pos a, Pos b) {
      if (a==null || a==Pos.UNKNOWN || b==null || b==Pos.UNKNOWN || !a.filename.equals(b.filename)) return false;
      return a.y2<b.y || (a.y2==b.y && a.x2<b.x);
   }

   /** Two Pos objects are equal if the filename x y x2 y2 are the same. */
   @Override public boolean equals(Object other) {
      if (this==other) return true;
      if (!(other instanceof Pos)) return false;
      Pos that = (Pos) other;
      return x==that.x && y==that.y && x2==that.x2 && y2==that.y2 && filename.equals(that.filename);
   }

   /** Returns a hash code consistent with equals() */
   @Override public int hashCode() {
      return x*111 + y*171 + x2*1731 + y2*2117;
   }

   /** Returns a short String representation of this position value. */
   public String toShortString() {
      String f=filename;
      int a=f.lastIndexOf('/'), b=f.lastIndexOf('\\');
      if (a<b) a=b;
      if (a>=0) f=f.substring(a+1);
      if (f.length()==0) return "line "+y+", column "+x; else return "line "+y+", column "+x+", filename="+f;
   }

   /** Returns a String representation of this position value. */
   @Override public String toString() {
      if (filename.length()==0) return "line "+y+", column "+x; else return "line "+y+", column "+x+", filename="+filename;
   }
}
