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

package edu.mit.csail.sdg.alloy4compiler.ast;

import edu.mit.csail.sdg.alloy4.Pos;

/** Immutable; represents attributes that can be associated with Signatures and some other AST objects. */

public final class Attr {

   /** This class contains all possible attribute types. */
   public enum AttrType {

      /** WHERE; if a Sig has a WHERE attribute, it defines where the sig was declared in the user model. */
      WHERE("where"),

      /** ABSTRACT; if a PrimSig is abstract, it is equal to the union of its subsigs. */
      ABSTRACT("abstract"),

      /** SOME; if a Sig is some, it has at least one atom. */
      SOME("some"),

      /** ONE; if a Sig is one, it has exactly one atom. */
      ONE("one"),

      /** LONE; if a Sig is lone, it has at most one atom. */
      LONE("lone"),

      /** EXACT; if a SubsetSig is exact, it is equal to the union of its parents. */
      EXACT("exact"),

      /** SUBSIG; every PrimSig (including the builtin sigs) has the SUBSIG attribute set, and the SUBSET attribute unset. */
      SUBSIG("subsig"),

      /** SUBSET; every SubsetSig has the SUBSET attribute set, and the SUBSIG attribute unset. */
      SUBSET("subset"),

      /** META; if a Sig has the META attribute, it means it is a META atom corresponding to some real signature or field. */
      META("meta"),

      /** PRIVATE; if a Sig has the PRIVATE attribute, it means its label is private within the same module. */
      PRIVATE("private"),

      /** BUILTIN; every builtin Sig has the BUILTIN attribute, and every non-builtin Sig does not. */
      BUILTIN("builtin"),

      /** ENUM; if a PrimSig has the ENUM attribute, it is toplevel and abstract and has only singleton children. */
      ENUM("enum");

      /** The label for this attribute type. */
      private final String label;

      /** Constructor for this attribute type. */
      private AttrType(String label) { this.label = label; }

      /** Construct an attribute of this type with this position; if pos==null, it is treated as Pos.UNKNOWN. */
      public final Attr make(Pos pos) { return new Attr(this, pos); }

      /** Construct an attribute of this type with this position; if pos==null, this method returns null. */
      public final Attr makenull(Pos pos) { return pos==null ? null : new Attr(this, pos); }

      /** Returns the combined position for all Attribute of this type in the given array; null entries in the collection are ignored; if none are found we return null. */
      public Pos find(Attr... attributes) {
         Pos p = null;
         if (attributes!=null) for(Attr a: attributes) if (a!=null && a.type==this) p = a.pos.merge(p);
         return p;
      }

      /** {@inheritDoc} */
      @Override public final String toString() { return label; }
   }

   /** The type of this attribute. */
   public final AttrType type;

   /** The position associated with this attribute. */
   public final Pos pos;

   /** ABSTRACT; if a PrimSig is abstract, it is equal to the union of its subsigs. */
   public static final Attr ABSTRACT = new Attr(AttrType.ABSTRACT, null);

   /** SOME; if a Sig is some, it has at least one atom. */
   public static final Attr SOME = new Attr(AttrType.SOME, null);

   /** ONE; if a Sig is one, it has exactly one atom. */
   public static final Attr ONE = new Attr(AttrType.ONE, null);

   /** LONE; if a Sig is lone, it has at most one atom. */
   public static final Attr LONE = new Attr(AttrType.LONE, null);

   /** EXACT; if a SubsetSig is exact, it is equal to the union of its parents. */
   public static final Attr EXACT = new Attr(AttrType.EXACT, null);

   /** SUBSIG; every PrimSig (including the builtin sigs) has the SUBSIG attribute set, and the SUBSET attribute unset. */
   public static final Attr SUBSIG = new Attr(AttrType.SUBSIG, null);

   /** SUBSET; every SubsetSig has the SUBSET attribute set, and the SUBSIG attribute unset. */
   public static final Attr SUBSET = new Attr(AttrType.SUBSET, null);

   /** META; if a Sig has the META attribute, it means it is a META atom corresponding to some real signature or field. */
   public static final Attr META = new Attr(AttrType.META, null);

   /** PRIVATE; if a Sig has the PRIVATE attribute, it means its label is private within the same module. */
   public static final Attr PRIVATE = new Attr(AttrType.PRIVATE, null);

   /** BUILTIN; every builtin Sig has the BUILTIN attribute, and every non-builtin Sig does not. */
   public static final Attr BUILTIN = new Attr(AttrType.BUILTIN, null);

   /** ENUM; if a PrimSig has the ENUM attribute, it is toplevel and abstract and has only singleton children. */
   public static final Attr ENUM = new Attr(AttrType.ENUM, null);

   /** Construct an attribute of the given type with the given position; if pos==null, it is treated as Pos.UNKNOWN. */
   private Attr(AttrType type, Pos pos) {
      this.type = type;
      this.pos = (pos==null ? Pos.UNKNOWN : pos);
   }

   /** {@inheritDoc} */
   @Override public final String toString() { return type.label; }
}
