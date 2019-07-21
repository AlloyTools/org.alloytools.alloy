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

package edu.mit.csail.sdg.ast;

import static edu.mit.csail.sdg.alloy4.TableView.clean;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ConstList.TempList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4.Version;
import edu.mit.csail.sdg.ast.Attr.AttrType;

/** Mutable; represents a signature. */

public abstract class Sig extends Expr implements Clause {

    /** The built-in "univ" signature. */
    public static final PrimSig UNIV   = new PrimSig("univ", null, false);

    /** The built-in "Int" signature. */
    public static final PrimSig SIGINT = new PrimSig("Int", UNIV, false);

    /** The built-in "seq/Int" signature. */
    public static final PrimSig SEQIDX = new PrimSig("seq/Int", SIGINT, true);

    /** The built-in "String" signature. */
    public static final PrimSig STRING = new PrimSig("String", UNIV, true);

    /** The built-in "none" signature. */
    public static final PrimSig NONE   = new PrimSig("none", null, false);

    /** The built-in "none" signature. */
    public static final PrimSig GHOST  = mkGhostSig();

    private static final PrimSig mkGhostSig() {
        try {
            return new PrimSig("Univ", null, new Attr[0]);
        } catch (Err e) {
            return null; // never happens
        }
    }

    /**
     * Returns the name for this sig; this name need not be unique.
     */
    @Override
    public final String toString() {
        return label;
    }

    public String toExtendedString() {
        StringBuilder sb = new StringBuilder();
        if (this.builtin) {
            sb.append("builtin ");
        }
        if (isPrivate != null)
            sb.append("private ");
        if (isAbstract != null)
            sb.append("abstract ");

        if (isLone != null)
            sb.append("lone ");

        if (isOne != null)
            sb.append("one ");

        if (isOne != null)
            sb.append("some ");

        if (isSubset != null)
            sb.append("subset ");

        if (isMeta != null)
            sb.append("meta ");

        if (isEnum != null)
            sb.append("enum ");

        sb.append(label).append("{");
        String del = "";
        for (Field f : realFields) {
            sb.append(del);
            sb.append(f.label);
            del = ", ";
        }
        sb.append("}");
        return sb.toString();
    }

    /** {@inheritDoc} */
    @Override
    public final void toString(StringBuilder out, int indent) {
        if (indent < 0) {
            out.append(label);
        } else {
            for (int i = 0; i < indent; i++) {
                out.append(' ');
            }
            out.append("sig ").append(label).append(" with type=").append(type).append('\n');
        }
    }

    /** {@inheritDoc} */
    @Override
    public final Pos span() {
        return pos;
    }

    /** {@inheritDoc} */
    @Override
    public Expr resolve(Type t, Collection<ErrorWarning> warns) {
        return this;
    }

    /** {@inheritDoc} */
    @Override
    public final <T> T accept(VisitReturn<T> visitor) throws Err {
        return visitor.visit(this);
    }

    /**
     * Store the list of attributes.
     */
    public final ConstList<Attr> attributes;

    /**
     * True if this sig is one of the built-in sig.
     * <p>
     * Note: if builtin==true, then we ensure it is not abstract
     */
    public final boolean         builtin;

    /**
     * Nonnull if this sig is abstract.
     * <p>
     * Note: if a sig is abstract, then it cannot and will not be a subset sig.
     */
    public final Pos             isAbstract;

    /**
     * Nonnull if this sig is a PrimSig and therefore not a SubsetSig.
     */
    public final Pos             isSubsig;

    /**
     * Nonnull if this sig is a SubsetSig and therefore not a PrimSig.
     * <p>
     * Note: if a sig is a subset sig, then it cannot and will not be abstract.
     */
    public final Pos             isSubset;

    /**
     * Nonnull if this sig's multiplicity is declared to be lone.
     * <p>
     * Note: at most one of "lone", "one", "some" can be nonnull for each sig.
     */
    public final Pos             isLone;

    /**
     * Nonnull if this sig's multiplicity is declared to be one.
     * <p>
     * Note: at most one of "lone", "one", "some" can be nonnull for each sig.
     */
    public final Pos             isOne;

    /**
     * Nonnull if this sig's multiplicity is declared to be some.
     * <p>
     * Note: at most one of "lone", "one", "some" can be nonnull for each sig.
     */
    public final Pos             isSome;

    /**
     * Nonnull if the user wanted this sig to be private.
     * <p>
     * Note: this value is always null for builtin sigs.
     */
    public final Pos             isPrivate;

    /**
     * Nonnull if the sig is toplevel and is an enum.
     * <p>
     * Note: this value is always null for builtin sigs.
     */
    public final Pos             isEnum;

    /**
     * Nonnull if this sig is a meta sig.
     * <p>
     * Note: this value is always null for builtin sigs.
     */
    public final Pos             isMeta;

    /**
     * The label for this sig; this name does not need to be unique.
     */
    public final String          label;

    /**
     * The declaration that quantifies over each atom in this sig.
     */
    public final Decl            decl;

    /**
     * The list of "per atom" fact associated with this signature; each fact is
     * allowed to refer to this.decl.get()
     */
    private final SafeList<Expr> facts = new SafeList<Expr>();

    /**
     * Returns true if this sig is a toplevel sig (meaning: it is UNIV, or it is a
     * non-subset sig with parent==UNIV)
     */
    public final boolean isTopLevel() {
        return (this != NONE) && (this instanceof PrimSig) && (this == UNIV || ((PrimSig) this).parent == UNIV);
    }

    /** Constructs a new builtin PrimSig. */
    private Sig(String label) {
        super(Pos.UNKNOWN, null);
        Expr oneof = ExprUnary.Op.ONEOF.make(null, this);
        ExprVar v = ExprVar.make(null, "this", oneof.type);
        this.decl = new Decl(null, null, null, Util.asList(v), oneof);
        this.builtin = true;
        this.isAbstract = null;
        this.isLone = null;
        this.isOne = null;
        this.isSome = null;
        this.label = label;
        this.isSubset = null;
        this.isSubsig = Pos.UNKNOWN;
        this.isPrivate = null;
        this.isMeta = null;
        this.isEnum = null;
        this.attributes = ConstList.make();
    }

    /** Constructs a new PrimSig or SubsetSig. */
    private Sig(Type type, String label, Attr... attributes) throws Err {
        super(AttrType.WHERE.find(attributes), type);
        this.attributes = Util.asList(attributes);
        Expr oneof = ExprUnary.Op.ONEOF.make(null, this);
        ExprVar v = ExprVar.make(null, "this", oneof.type);
        this.decl = new Decl(null, null, null, Util.asList(v), oneof);
        Pos isAbstract = null, isLone = null, isOne = null, isSome = null, isSubsig = null, isSubset = null,
                        isPrivate = null, isMeta = null, isEnum = null;
        for (Attr a : attributes)
            if (a != null)
                switch (a.type) {
                    case ABSTRACT :
                        isAbstract = a.pos.merge(isAbstract);
                        break;
                    case ENUM :
                        isEnum = a.pos.merge(isEnum);
                        break;
                    case LONE :
                        isLone = a.pos.merge(isLone);
                        break;
                    case META :
                        isMeta = a.pos.merge(isMeta);
                        break;
                    case ONE :
                        isOne = a.pos.merge(isOne);
                        break;
                    case PRIVATE :
                        isPrivate = a.pos.merge(isPrivate);
                        break;
                    case SOME :
                        isSome = a.pos.merge(isSome);
                        break;
                    case SUBSET :
                        isSubset = a.pos.merge(isSubset);
                        break;
                    case SUBSIG :
                        isSubsig = a.pos.merge(isSubsig);
                        break;
                    default :
                        //TODO throw new ErrorWarning("Undefined case " + a);
                }
        this.isPrivate = isPrivate;
        this.isMeta = isMeta;
        this.isEnum = isEnum;
        this.isAbstract = isAbstract;
        this.isLone = isLone;
        this.isOne = isOne;
        this.isSome = isSome;
        this.isSubset = isSubset;
        this.isSubsig = isSubsig;
        this.label = label;
        this.builtin = false;
        if (isLone != null && isOne != null)
            throw new ErrorSyntax(isLone.merge(isOne), "You cannot declare a sig to be both lone and one.");
        if (isLone != null && isSome != null)
            throw new ErrorSyntax(isLone.merge(isSome), "You cannot declare a sig to be both lone and some.");
        if (isOne != null && isSome != null)
            throw new ErrorSyntax(isOne.merge(isSome), "You cannot declare a sig to be both one and some.");
        if (isSubset != null && isAbstract != null)
            throw new ErrorSyntax(isAbstract, "Subset signature cannot be abstract.");
        if (isSubset != null && isSubsig != null)
            throw new ErrorSyntax(isAbstract, "Subset signature cannot be a regular subsignature.");
    }

    /**
     * Returns true if we can determine the two expressions are equivalent; may
     * sometimes return false.
     */
    @Override
    public boolean isSame(Expr obj) {
        Sig me = this;
        while (obj instanceof ExprUnary && ((ExprUnary) obj).op == ExprUnary.Op.NOOP)
            obj = ((ExprUnary) obj).sub;
        while (obj instanceof SubsetSig && ((SubsetSig) obj).exact && ((SubsetSig) obj).parents.size() == 1)
            obj = ((SubsetSig) obj).parents.get(0);
        while (me instanceof SubsetSig && ((SubsetSig) me).exact && ((SubsetSig) me).parents.size() == 1)
            me = ((SubsetSig) me).parents.get(0);
        return (me == obj);
    }

    /** Returns true iff "this is equal or subtype of that" */
    public abstract boolean isSameOrDescendentOf(Sig that);

    /** {@inheritDoc} */
    @Override
    public int getDepth() {
        return 1;
    }

    /**
     * Add a new per-atom fact; this expression is allowed to refer to
     * this.decl.get()
     */
    public void addFact(Expr fact) throws Err {
        if (fact.ambiguous)
            fact = fact.resolve_as_formula(null);
        if (!fact.errors.isEmpty())
            throw fact.errors.pick();
        if (!fact.type.is_bool)
            throw new ErrorType(fact.span(), "This expression must be a formula; instead its type is " + fact.type);
        facts.add(fact);
    }

    /**
     * Return the list of per-atom facts; each expression is allowed to refer to
     * this.decl.get()
     */
    public SafeList<Expr> getFacts() {
        return facts.dup();
    }

    /** {@inheritDoc} */
    @Override
    public final String getHTML() {
        return "<b>sig</b> " + label + " <i>" + type + "</i>";
    }

    /** {@inheritDoc} */
    @Override
    public final List< ? extends Browsable> getSubnodes() {
        TempList<Browsable> ans = new TempList<Browsable>();
        if (this instanceof PrimSig) {
            Sig parent = ((PrimSig) this).parent;
            if (parent != null && !parent.builtin)
                ans.add(make(parent.pos, parent.span(), "<b>extends sig</b> " + parent.label, parent.getSubnodes()));
        } else {
            ConstList<Sig> parents = ((SubsetSig) this).parents;
            for (Sig p : parents)
                ans.add(make(p.pos, p.span(), "<b>in sig</b> " + p.label, p.getSubnodes()));
        }
        for (Decl d : fields)
            for (ExprHasName v : d.names) {
                ans.add(make(v.span(), v.span(), "<b>field</b> " + v.label + " <i>" + v.type + "</i>", d.expr));
            }
        for (Expr f : facts)
            ans.add(make(f.span(), f.span(), "<b>fact</b>", f));
        return ans.makeConst();
    }

    // ==============================================================================================================//

    /**
     * Mutable; reresents a non-subset signature.
     * <p>
     * Note: except for "children()", the return value of every method is always
     * valid for all time; for example, given sigs A and B, and you call
     * C=A.intersect(B), then the result C will always be the intersection of A and
     * B even if the caller later constructs more sigs or subsigs or subsetsigs...
     */

    public static final class PrimSig extends Sig {

        /**
         * Stores its immediate children sigs (not including NONE)
         * <p>
         * Note: if this==UNIV, then this list will always be empty, since we don't keep
         * track of UNIV's children
         */
        private final SafeList<PrimSig> children = new SafeList<PrimSig>();

        /**
         * Returns its immediate children sigs (not including NONE)
         * <p>
         * Note: if this==UNIV, then this method will throw an exception, since we don't
         * keep track of UNIV's children
         */
        public SafeList<PrimSig> children() throws Err {
            if (this == UNIV)
                throw new ErrorFatal("Internal error (cannot enumerate the subsigs of UNIV)");
            return children.dup();
        }

        /**
         * Returns its subsigs and their subsigs and their subsigs, etc.
         * <p>
         * Note: if this==UNIV, then this method will throw an exception, since we don't
         * keep track of UNIV's children
         */
        public Iterable<PrimSig> descendents() throws Err {
            if (this == UNIV)
                throw new ErrorFatal("Internal error (cannot enumerate the subsigs of UNIV)");
            Iterable<PrimSig> answer = children.dup();
            for (PrimSig x : children)
                answer = Util.fastJoin(answer, x.descendents());
            return answer;
        }

        /**
         * If this is UNIV or NONE, then this field is null, else this field is the
         * parent sig.
         */
        public final PrimSig parent;

        /** Constructs a builtin PrimSig. */
        private PrimSig(String label, PrimSig parent, boolean add) {
            super(label);
            this.parent = parent;
            if (add)
                this.parent.children.add(this);
        }

        /**
         * Constructs a non-builtin sig.
         *
         * @param label - the name of this sig (it does not need to be unique)
         * @param parent - the parent (must not be null, and must not be NONE)
         * @param attributes - the list of optional attributes such as ABSTRACT, LONE,
         *            ONE, SOME, SUBSIG, PRIVATE, META, or ENUM
         * @throws ErrorSyntax if the signature has two or more multiplicities
         * @throws ErrorType if you attempt to extend the builtin sigs NONE, SIGINT,
         *             SEQIDX, or STRING
         */
        public PrimSig(String label, PrimSig parent, Attr... attributes) throws Err {
            super(((parent != null && parent.isEnum != null) ? parent.type : null), label, Util.append(attributes, Attr.SUBSIG));
            if (parent == SIGINT)
                throw new ErrorSyntax(pos, "sig " + label + " cannot extend the builtin \"Int\" signature");
            if (parent == SEQIDX)
                throw new ErrorSyntax(pos, "sig " + label + " cannot extend the builtin \"seq/Int\" signature");
            if (parent == STRING)
                throw new ErrorSyntax(pos, "sig " + label + " cannot extend the builtin \"String\" signature");
            if (parent == NONE)
                throw new ErrorSyntax(pos, "sig " + label + " cannot extend the builtin \"none\" signature");
            if (parent == null)
                parent = UNIV;
            else if (parent != UNIV)
                parent.children.add(this);
            this.parent = parent;
            if (isEnum != null && parent != UNIV)
                throw new ErrorType(pos, "sig " + label + " is not a toplevel sig, so it cannot be an enum.");
            for (; parent != null; parent = parent.parent)
                if (parent.isEnum != null) {
                    if (parent != this.parent)
                        throw new ErrorSyntax(pos, "sig " + label + " cannot extend a signature which is an atom in an enum.");
                    if (isOne == null)
                        throw new ErrorSyntax(pos, "sig " + label + " is an atom in an enum, so it must have the \"one\" multiplicity.");
                }
        }

        /**
         * Constructs a toplevel non-builtin sig.
         *
         * @param label - the name of this sig (it does not need to be unique)
         * @param attributes - the list of optional attributes such as ABSTRACT, LONE,
         *            ONE, SOME, SUBSIG, PRIVATE, META, or ENUM
         * @throws ErrorSyntax if the signature has two or more multiplicities
         */
        public PrimSig(String label, Attr... attributes) throws Err {
            this(label, null, attributes);
        }

        /** {@inheritDoc} */
        @Override
        public boolean isSameOrDescendentOf(Sig that) {
            if (this == NONE || this == that || that == UNIV)
                return true;
            if (this == UNIV || that == NONE)
                return false;
            for (PrimSig me = this; me != null; me = me.parent)
                if (me == that)
                    return true;
            return false;
        }

        /**
         * Returns the intersection between this and that (and returns "none" if they do
         * not intersect).
         */
        public PrimSig intersect(PrimSig that) {
            if (this.isSameOrDescendentOf(that))
                return this;
            if (that.isSameOrDescendentOf(this))
                return that;
            return NONE;
        }

        /**
         * Returns true iff the intersection between this and that is not "none".
         */
        public boolean intersects(PrimSig that) {
            if (this.isSameOrDescendentOf(that))
                return this != NONE;
            if (that.isSameOrDescendentOf(this))
                return that != NONE;
            return false;
        }

        /**
         * Returns the most-specific-sig that contains this and that. In particular, if
         * this extends that, then return that.
         */
        public PrimSig leastParent(PrimSig that) {
            if (isSameOrDescendentOf(that))
                return that;
            PrimSig me = this;
            while (true) {
                if (that.isSameOrDescendentOf(me))
                    return me;
                me = me.parent;
                if (me == null)
                    return UNIV;
            }
        }
    }

    // ==============================================================================================================//

    /** Mutable; reresents a subset signature. */

    public static final class SubsetSig extends Sig {

        /**
         * The list of Sig that it is a subset of; this list is never empty.
         */
        public final ConstList<Sig> parents;

        /**
         * If true, then this sig is EXACTLY equal to the union of its parents.
         */
        public final boolean        exact;

        /** Computes the type for this sig. */
        private static Type getType(String label, Iterable<Sig> parents) throws Err {
            Type ans = null;
            if (parents != null)
                for (Sig parent : parents) {
                    if (parent == UNIV)
                        return UNIV.type;
                    if (ans == null)
                        ans = parent.type;
                    else
                        ans = ans.unionWithCommonArity(parent.type);
                }
            return (ans != null) ? ans : (UNIV.type);
        }

        /**
         * Constructs a subset sig.
         *
         * @param label - the name of this sig (it does not need to be unique)
         * @param parents - the list of parents (if this list is null or empty, we
         *            assume the caller means UNIV)
         * @param attributes - the list of optional attributes such as EXACT, SUBSET,
         *            LONE, ONE, SOME, PRIVATE, or META
         * @throws ErrorSyntax if the signature has two or more multiplicities
         * @throws ErrorType if parents only contains NONE
         */
        public SubsetSig(String label, Collection<Sig> parents, Attr... attributes) throws Err {
            super(getType(label, parents), label, Util.append(attributes, Attr.SUBSET));
            if (isEnum != null)
                throw new ErrorType(pos, "Subset signature cannot be an enum.");
            boolean exact = false;
            for (Attr a : attributes)
                if (a != null && a.type == AttrType.EXACT)
                    exact = true;
            this.exact = exact;
            TempList<Sig> temp = new TempList<Sig>(parents == null ? 1 : parents.size());
            if (parents == null || parents.size() == 0) {
                temp.add(UNIV);
            } else {
                for (Sig parent : parents) {
                    if (!Version.experimental) {
                        if (parent == SIGINT)
                            throw new ErrorSyntax(pos, "sig " + label + " cannot be a subset of the builtin \"Int\" signature");
                        if (parent == SEQIDX)
                            throw new ErrorSyntax(pos, "sig " + label + " cannot be a subset of the builtin \"seq/Int\" signature");
                        if (parent == STRING)
                            throw new ErrorSyntax(pos, "sig " + label + " cannot be a subset of the builtin \"String\" signature");
                    }
                    if (parent == Sig.UNIV) {
                        temp.clear();
                        temp.add(UNIV);
                        break;
                    }
                    if (parent != Sig.NONE && !temp.contains(parent))
                        temp.add(parent);
                }
            }
            if (temp.size() == 0)
                throw new ErrorType(pos, "Sig " + label + " must have at least one non-empty parent.");
            this.parents = temp.makeConst();
        }

        /** {@inheritDoc} */
        @Override
        public boolean isSameOrDescendentOf(Sig that) {
            if (that == UNIV || that == this)
                return true;
            if (that == NONE)
                return false;
            for (Sig p : parents)
                if (p.isSameOrDescendentOf(that))
                    return true;
            return false;
        }
    }

    // ==============================================================================================================//

    /** Mutable; represents a field. */

    public static final class Field extends ExprHasName implements Clause {

        /** The sig that this field belongs to; never null. */
        public final Sig     sig;

        /** Nonnull if the user wanted this field to be private. */
        public final Pos     isPrivate;

        /** Nonnull if this field is a meta field. */
        public final Pos     isMeta;

        /** True if this is a defined field. */
        public final boolean defined;

        /** The declaration that this field came from. */
        private Decl         decl;

        /** Return the declaration that this field came from. */
        public Decl decl() {
            return decl;
        }

        /** Constructs a new Field object. */
        private Field(Pos pos, Pos isPrivate, Pos isMeta, Pos disjoint, Pos disjoint2, Sig sig, String label, Expr bound) throws Err {
            super(pos, label, sig.type.product(bound.type));
            this.defined = bound.mult() == ExprUnary.Op.EXACTLYOF;
            if (sig.builtin)
                throw new ErrorSyntax(pos, "Builtin sig \"" + sig + "\" cannot have fields.");
            if (!bound.errors.isEmpty())
                throw bound.errors.pick();
            if (!this.defined && bound.hasCall())
                throw new ErrorSyntax(pos, "Field \"" + label + "\" declaration cannot contain a function or predicate call.");
            if (bound.type.arity() > 0 && bound.type.hasNoTuple())
                throw new ErrorType(pos, "Cannot bind field " + label + " to the empty set or empty relation.");
            this.isPrivate = (isPrivate != null ? isPrivate : sig.isPrivate);
            this.isMeta = (isMeta != null ? isMeta : sig.isMeta);
            this.sig = sig;
        }

        /**
         * Returns a human-readable description of this field's name.
         */
        @Override
        public String toString() {
            if (sig.label.length() == 0)
                return label;
            else
                return "field (" + sig + " <: " + label + ")";
        }

        /** {@inheritDoc} */
        @Override
        public void toString(StringBuilder out, int indent) {
            if (indent < 0) {
                out.append("(").append(sig.label).append(" <: ").append(label).append(")");
            } else {
                for (int i = 0; i < indent; i++) {
                    out.append(' ');
                }
                out.append("field ").append(sig.label).append(" <: ").append(label).append(" with type=").append(type).append('\n');
            }
        }

        /** {@inheritDoc} */
        @Override
        public Expr resolve(Type t, Collection<ErrorWarning> warns) {
            return this;
        }

        /** {@inheritDoc} */
        @Override
        public final <T> T accept(VisitReturn<T> visitor) throws Err {
            return visitor.visit(this);
        }

        /** {@inheritDoc} */
        @Override
        public String getHTML() {
            return "<b>field</b> " + label + " <i>" + type + "</i>";
        }

        /** {@inheritDoc} */
        @Override
        public List< ? extends Browsable> getSubnodes() {
            Expr bound = decl.expr;
            Browsable s = make(sig.pos, sig.span(), "<b>from sig</b> " + sig.label, sig.getSubnodes());
            Browsable b = make(bound.span(), bound.span(), "<b>bound</b>", bound);
            return Util.asList(s, b);
        }

        @Override
        public String explain() {

            StringBuilder sb = new StringBuilder();

            if (isPrivate != null) {
                sb.append("private ");
            }
            if (isMeta != null) {
                sb.append("meta ");
            }
            sb.append(clean(label));
            sb.append(" : ").append(clean(type.explain()));
            return sb.toString();
        }

    }

    // ==============================================================================================================//

    /** The list of fields. */
    private final SafeList<Decl>  fields     = new SafeList<Decl>();
    private final SafeList<Field> realFields = new SafeList<>();

    /**
     * Return the list of fields as a unmodifiable list of declarations (where you
     * can see which fields are declared to be disjoint)
     */
    public final SafeList<Decl> getFieldDecls() {
        return fields.dup();
    }

    /**
     * Return the list of fields as a combined unmodifiable list (without telling
     * you which fields are declared to be disjoint)
     */
    public final SafeList<Field> getFields() {
        SafeList<Field> ans = new SafeList<Field>();
        for (Decl d : fields)
            for (ExprHasName n : d.names)
                ans.add((Field) n);
        return ans.dup();
    }

    /**
     * Add then return a new field, where "all x: ThisSig | x.F in bound"
     * <p>
     * Note: the bound must be fully-typechecked and have exactly 0 free variable,
     * or have "x" as its sole free variable.
     *
     * @param label - the name of this field (it does not need to be unique)
     * @param bound - the new field will be bound by "all x: one ThisSig |
     *            x.ThisField in bound"
     * @throws ErrorSyntax if the sig is one of the builtin sig
     * @throws ErrorSyntax if the bound contains a predicate/function call
     * @throws ErrorType if the bound is not fully typechecked or is not a
     *             set/relation
     */
    public final Field addField(String label, Expr bound) throws Err {
        bound = bound.typecheck_as_set();
        if (bound.ambiguous)
            bound = bound.resolve_as_set(null);
        if (bound.mult == 0 && bound.type.arity() == 1)
            bound = ExprUnary.Op.ONEOF.make(null, bound); // If unary, and no
                                                         // multiplicity
                                                         // symbol, we assume
                                                         // it's oneOf
        final Field f = new Field(null, null, null, null, null, this, label, bound);
        final Decl d = new Decl(null, null, null, Arrays.asList(f), bound);
        f.decl = d;
        fields.add(d);
        realFields.add(f);
        return f;
    }

    /**
     * Add then return a new field, where "all x: ThisSig | x.F in bound"
     * <p>
     * Note: the bound must be fully-typechecked and have exactly 0 free variable,
     * or have "x" as its sole free variable.
     *
     * @param pos - the position in the original file where this field was defined
     *            (can be null if unknown)
     * @param isPrivate - if nonnull, that means the user intended this field to be
     *            "private"
     * @param isMeta - if nonnull, that means the user intended this field to be
     *            "meta"
     * @param labels - the names of the fields to be added (these names does not
     *            need to be unique)
     * @param bound - the new field will be bound by "all x: one ThisSig |
     *            x.ThisField in bound"
     * @throws ErrorSyntax if the sig is one of the builtin sig
     * @throws ErrorSyntax if the bound contains a predicate/function call
     * @throws ErrorType if the bound is not fully typechecked or is not a
     *             set/relation
     */
    public final Field[] addTrickyField(Pos pos, Pos isPrivate, Pos isDisjoint, Pos isDisjoint2, Pos isMeta, String[] labels, Expr bound) throws Err {
        bound = bound.typecheck_as_set();
        if (bound.ambiguous)
            bound = bound.resolve_as_set(null);
        if (bound.mult == 0 && bound.type.arity() == 1)
            bound = ExprUnary.Op.ONEOF.make(null, bound); // If unary, and no
                                                         // multiplicity
                                                         // symbol, we assume
                                                         // it's oneOf
        final Field[] f = new Field[labels.length];
        for (int i = 0; i < f.length; i++)
            f[i] = new Field(pos, isPrivate, isMeta, isDisjoint, isDisjoint2, this, labels[i], bound);
        final Decl d = new Decl(isPrivate, isDisjoint, isDisjoint2, Arrays.asList(f), bound);
        for (int i = 0; i < f.length; i++) {
            f[i].decl = d;
            realFields.add(f[i]);
        }
        fields.add(d);
        return f;
    }

    /**
     * Add then return a new field F where this.F is bound to an exact "definition"
     * expression.
     * <p>
     * Note: the definition must be fully-typechecked and have exactly 0 free
     * variables.
     * <p>
     * Note: currently the defined field must consist product and union operators
     * over sigs.
     *
     * @param pos - the position in the original file where this field was defined
     *            (can be null if unknown)
     * @param isPrivate - if nonnull, that means this field should be marked as
     *            private
     * @param isMeta - if nonnull, that means this field should be marked as meta
     * @param label - the name of this field (it does not need to be unique)
     * @param bound - the new field will be defined to be exactly equal to
     *            sig.product(definition)
     * @throws ErrorSyntax if the sig is one of the builtin sig
     * @throws ErrorSyntax if the bound contains a predicate/function call
     * @throws ErrorType if the bound is not fully typechecked or is not a
     *             set/relation
     */
    public final Field addDefinedField(Pos pos, Pos isPrivate, Pos isMeta, String label, Expr bound) throws Err {
        bound = bound.typecheck_as_set();
        if (bound.ambiguous)
            bound = bound.resolve_as_set(null);
        if (bound.mult() != ExprUnary.Op.EXACTLYOF)
            bound = ExprUnary.Op.EXACTLYOF.make(null, bound);
        final Field f = new Field(pos, isPrivate, isMeta, null, null, this, label, bound);
        final Decl d = new Decl(null, null, null, Arrays.asList(f), bound);
        f.decl = d;
        fields.add(d);
        realFields.add(f);
        return f;
    }

    @Override
    public String explain() {
        StringBuilder sb = new StringBuilder();
        if (builtin)
            sb.append("builtin ");
        if (isEnum != null)
            sb.append("enum ");
        if (isAbstract != null)
            sb.append("abstract ");
        if (isLone != null)
            sb.append("lone ");
        if (isOne != null)
            sb.append("one ");
        if (isMeta != null)
            sb.append("meta ");
        if (isSome != null)
            sb.append("some ");
        if (isSubsig != null)
            sb.append("sig ");
        if (isSubset != null)
            sb.append("subset ");

        sb.append(clean(label)).append(" { ");
        String del = "";
        for (Field f : realFields) {
            String relation = clean(type.join(f.type).explain());
            sb.append(del).append(f.label).append(" : ").append(relation);
            del = ", ";
        }
        sb.append(" }");

        return sb.toString();
    }
}
