/*
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package kodkod.ast;

import kodkod.ast.operator.Multiplicity;
import kodkod.ast.visitor.ReturnVisitor;
import kodkod.ast.visitor.VoidVisitor;

/**
 * Represents common predicates on relations; e.g. predicates stating that a
 * relation is a total function, partial function, acyclic, or a total ordering
 * over a set of atoms.
 *
 * @specfield relation: Relation
 * @specfield name: Name // name of the predicate
 * @invariant relation.arity = 2
 * @author Emina Torlak
 */
public abstract class RelationPredicate extends Formula {

    private final Relation relation;

    /**
     * Constructs a new relation predicate for the given relation.
     *
     * @throws NullPointerException relation = null
     * @throws IllegalArgumentException relation.arity != 2
     */
    private RelationPredicate(Relation relation) {
        if (relation.arity() != 2)
            throw new IllegalArgumentException("invalid arity: " + relation.arity());
        this.relation = relation;
    }

    /**
     * Returns the relation to which this predicate applies.
     *
     * @return this.relation
     */
    public Relation relation() {
        return relation;
    }

    /**
     * Returns the name of this predicate.
     *
     * @return this.name
     */
    public abstract Name name();

    /**
     * Turns this predicate into explicit constraiants.
     *
     * @return {f: Formula - RelationPredicate | f <=> this }
     */
    public abstract Formula toConstraints();

    /**
     * {@inheritDoc}
     *
     * @see kodkod.ast.Formula#accept(kodkod.ast.visitor.ReturnVisitor)
     */
    @Override
    public <E, F, D, I> F accept(ReturnVisitor<E,F,D,I> visitor) {
        return visitor.visit(this);
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.ast.Node#accept(kodkod.ast.visitor.VoidVisitor)
     */
    @Override
    public void accept(VoidVisitor visitor) {
        visitor.visit(this);
    }

    /**
     * Enumerates built-in predicates.
     */
    public static enum Name {
                             /** Function predicate. */
                             FUNCTION,
                             /** Partial function predicate. */
                             // PARTIAL_FUNCTION,
                             /** Acyclic predicate. */
                             ACYCLIC,
                             /** Total ordering predicate. */
                             TOTAL_ORDERING
    }

    /**
     * Represents the acyclic predicate. The predicate states that the given
     * <code>relation</code> is acyclic.
     *
     * @specfield relation: Relation
     * @invariant name = ACYCLIC
     * @invariant children = 0->relation
     * @author Emina Torlak
     */
    public static final class Acyclic extends RelationPredicate {

        /**
         * Constructs a new acyclic predicate over the given relation.
         *
         * @ensures this.relation' = relation && this.name' = ACYCLIC
         * @throws IllegalArgumentException relation.arity != 2
         */
        Acyclic(Relation relation) {
            super(relation);
        }

        /**
         * Returns the name of this predicate.
         *
         * @return ACYCLIC
         */
        @Override
        public Name name() {
            return Name.ACYCLIC;
        }

        /**
         * {@inheritDoc}
         *
         * @see kodkod.ast.RelationPredicate#toConstraints()
         */
        @Override
        public Formula toConstraints() {
            return relation().closure().intersection(Expression.IDEN).no();
        }

        /**
         * {@inheritDoc}
         *
         * @see kodkod.ast.Node#toString()
         */
        @Override
        public String toString() {
            return name() + "(" + relation() + ")";
        }
    }

    /**
     * Represents the function predicate. The predicate states that the given
     * <code>relation</code> is a total or partial function with the specified
     * <code>domain</code> and <code>range</code>.
     *
     * @specfield relation: Relation
     * @specfield domain, range: Expression
     * @specfield targetMult: ONE + LONE
     * @invariant name = FUNCTION
     * @invariant domain.arity = range.arity = 1
     * @invariant children = 0->relation + 1->domain + 2->range
     * @author Emina Torlak
     */
    public static final class Function extends RelationPredicate {

        private final Expression   domain, range;
        private final Multiplicity targetMult;

        /**
         * Constructs a new function predicate over the given relation and domain, with
         * the specified target multiplicity.
         *
         * @ensures this.name' = FUNCTION && this.relation' = relation && this.domain' =
         *          domain && this.range' = range
         * @throws IllegalArgumentException relation.arity != 2 || domain.arity != 1 ||
         *             range.arity != 1 || targetMult !in ONE + LONE
         */
        Function(Relation relation, Expression domain, Multiplicity targetMult, Expression range) {
            super(relation);
            if (targetMult != Multiplicity.ONE && targetMult != Multiplicity.LONE)
                throw new IllegalArgumentException("invalid target multiplicity for a function: " + targetMult);
            if (domain.arity() != 1 || range.arity() != 1)
                throw new IllegalArgumentException("invalid arity: " + domain + " or " + range);
            this.targetMult = targetMult;
            this.domain = domain;
            this.range = range;
        }

        /**
         * Returns the name of this predicate.
         *
         * @return this.name
         */
        @Override
        public Name name() {
            return Name.FUNCTION;
        }

        /**
         * Returns the target multiplicity of the function represented by this.relation.
         *
         * @return this.targetMult
         */
        public Multiplicity targetMult() {
            return targetMult;
        }

        /**
         * Returns the domain of this.relation.
         *
         * @return this.domain
         */
        public Expression domain() {
            return domain;
        }

        /**
         * Returns the range of this.relation.
         *
         * @return this.range
         */
        public Expression range() {
            return range;
        }

        /**
         * {@inheritDoc}
         *
         * @see kodkod.ast.RelationPredicate#toConstraints()
         */
        @Override
        public Formula toConstraints() {
            // relation in domain->range
            final Formula domainConstraint = relation().in(domain.product(range));
            // all v: domain | targetMult v.relation
            final Variable v = Variable.unary("v" + relation().name());
            final Formula funConstraint = v.join(relation()).apply(targetMult).forAll(v.oneOf(domain));
            // relation in domain->range && all v: domain | targetMult
            // v.relation
            return domainConstraint.and(funConstraint);
        }

        /**
         * {@inheritDoc}
         *
         * @see kodkod.ast.Node#toString()
         */
        @Override
        public String toString() {
            return name() + "(" + relation() + ", " + domain + " ->" + targetMult + " " + range + ")";
        }
    }

    /**
     * Represents the total ordering predicate. The predicate states that the given
     * <code>relation</code> imposes a total ordering over the set
     * <code>ordered</code>, and that the smallest/largest elements resulting from
     * the ordering are given by the <code>first</code>/<code>last</code> relations.
     *
     * @specfield relation: Relation
     * @specfield ordered, first, last: Relation
     * @invariant name = TOTAL_ORDERING
     * @invariant ordered.arity = first.arity = last.arity = 1
     * @invariant children = 0->relation + 1->ordered + 2->first + 3->last
     */
    public static final class TotalOrdering extends RelationPredicate {

        private final Relation first, last, ordered;

        /**
         * Constructs a new total ordering predicate.
         *
         * @ensures this.relation' = relation && this.first' = first && this.last' =
         *          last && this.name' = TOTAL_ORDERING
         * @throws NullPointerException any of the arguments are null
         * @throws IllegalArgumentException relation.arity != 2 || first.arity != 1 ||
         *             last.arity != 1
         **/
        TotalOrdering(Relation relation, Relation ordered, Relation first, Relation last) {
            super(relation);
            if (first.arity() != 1 || last.arity() != 1 || ordered.arity() != 1)
                throw new IllegalArgumentException("invalid arity: " + first + " or " + last + " or " + ordered);
            this.first = first;
            this.last = last;
            this.ordered = ordered;
        }

        /**
         * Returns the name of this predicate.
         *
         * @return TOTAL_ORDERING
         */
        @Override
        public Name name() {
            return Name.TOTAL_ORDERING;
        }

        /**
         * Returns the relation representing the first element in the ordering imposed
         * by this.relation.
         *
         * @return this.first
         */
        public Relation first() {
            return first;
        }

        /**
         * Returns the relation representing the last element in the ordering imposed by
         * this.relation.
         *
         * @return this.last
         */
        public Relation last() {
            return last;
        }

        /**
         * Returns the relation representing the atoms which are ordered by
         * this.relation.
         *
         * @return this.ordered
         */
        public Relation ordered() {
            return ordered;
        }

        /**
         * {@inheritDoc}
         *
         * @see kodkod.ast.RelationPredicate#toConstraints()
         */
        @Override
        public Formula toConstraints() {
            // one first && one last && last in ordered
            final Formula f0 = first.one().and(last.one()).and(last.in(ordered));
            // ordered = first.*relation
            final Formula f1 = ordered.eq(first.join(relation().reflexiveClosure()));
            // no relation.first && no last.relation
            final Formula f2 = relation().join(first).no().and(last.join(relation()).no());
            // all e: ordered - last | one e.this
            final Variable e = Variable.unary("e" + relation().name());
            final Formula f3 = e.join(relation()).one().forAll(e.oneOf(ordered.difference(last)));

            return and(f0, f1, f2, f3);
        }

        /**
         * {@inheritDoc}
         *
         * @see kodkod.ast.Node#toString()
         */
        @Override
        public String toString() {
            return name() + "(" + relation() + ", " + ordered + ", " + first + ", " + last + ")";
        }

    }

}
