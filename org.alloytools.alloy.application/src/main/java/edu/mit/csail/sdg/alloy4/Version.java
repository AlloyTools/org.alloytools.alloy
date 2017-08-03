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

/** This holds the buildDate String.
 *
 * The release build script will generate a customized Version.java with the correct buildnumber and date.
 *
 * <p><b>Thread Safety:</b>  Safe.
 */

public final class Version {

   /** The constructor is private, since this class never needs to be instantiated. */
   private Version() { }

   /** This is true if this is an experimental version rather than a release version. */
   public static final boolean experimental = true;

   /** Returns the build number. */
   public static int buildNumber() { return Integer.MAX_VALUE; }

   /** Returns the version string. */
   public static String version() { return "4.2.?"; }

   /** Returns the build date. */
   public static String buildDate() { return "unknown"; }
   
}
