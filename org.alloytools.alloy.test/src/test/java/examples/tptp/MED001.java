/**
 *
 */
package examples.tptp;

import static kodkod.ast.Expression.IDEN;
import static kodkod.ast.Expression.UNIV;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 * A KK encoding of axioms MED001+0.ax and MED001+1.ax from
 * http://www.cs.miami.edu/~tptp/
 *
 * @author Emina Torlak
 */
public abstract class MED001 {

    protected final Relation bcapacityne, bcapacityex, bcapacitysn, conditionhyper, conditionhypo, conditionnormo,
                    drugi, uptakelg, uptakepg, releaselg, bsecretioni, drugbg, qilt27, s0, s1, s2, s3, drugsu, n0;
    protected final Relation gt;

    protected MED001() {
        bcapacityne = Relation.unary("bcapacityne");
        bcapacityex = Relation.unary("bcapacityex");
        bcapacitysn = Relation.unary("bcapacitysn");
        conditionhyper = Relation.unary("conditionhyper");
        conditionhypo = Relation.unary("conditionhypo");
        conditionnormo = Relation.unary("conditionnormo");
        drugi = Relation.unary("drugi");
        uptakelg = Relation.unary("uptakelg");
        uptakepg = Relation.unary("uptakepg");
        releaselg = Relation.unary("releaselg");
        bsecretioni = Relation.unary("bsecretioni");
        drugbg = Relation.unary("drugbg");
        qilt27 = Relation.unary("qilt27");
        s0 = Relation.unary("s0");
        s1 = Relation.unary("s1");
        s2 = Relation.unary("s2");
        s3 = Relation.unary("s3");
        drugsu = Relation.unary("drugsu");
        n0 = Relation.unary("n0");
        gt = Relation.binary("gt");
    }

    /**
     * Returns the declarations.
     *
     * @return declarations
     */
    public final Formula decls() {
        return n0.one();
    }

    /**
     * Returns the irreflexivity_gt axiom.
     *
     * @return irreflexivity_gt
     */
    public final Formula irreflexivity_gt() {
        return gt.intersection(IDEN).no();
    }

    /**
     * Returns the transitivity_gt axiom.
     *
     * @return transitivity_gt
     */
    public final Formula transitivity_gt() {
        return gt.join(gt).in(gt);
    }

    /**
     * Returns the axioms xorcapacity1 through xorcapacity1_4.
     *
     * @return xorcapacity1_4
     */
    public final Formula xorcapacity1_4() {
        return UNIV.in(bcapacityne.union(bcapacityex).union(bcapacitysn)).and(bcapacityne.intersection(bcapacityex).no()).and(bcapacityne.intersection(bcapacitysn).no()).and(bcapacityex.intersection(bcapacitysn).no());
    }

    /**
     * Returns the axioms xorcondition1 through xorcondition1.
     *
     * @return xorcondition1_4
     */
    public final Formula xorcondition1_4() {
        return UNIV.in(conditionhyper.union(conditionhypo).union(conditionnormo)).and(conditionhyper.intersection(conditionhypo).no()).and(conditionhyper.intersection(conditionnormo).no()).and(conditionnormo.intersection(conditionhypo).no());
    }

    /**
     * Returns the insulin_effect axiom.
     *
     * @return insulin_effect
     */
    public final Formula insulin_effect() {
        final Variable x0 = Variable.unary("X0");
        final Expression x1 = UNIV.difference(x0.join(gt));
        return x1.in(drugi).implies(x1.in(uptakelg.intersection(uptakepg))).forAll(x0.oneOf(UNIV));
    }

    /**
     * Returns the liver_glucose axiom.
     *
     * @return liver_glucose
     */
    public final Formula liver_glucose() {
        final Variable x0 = Variable.unary("X0");
        final Expression x1 = UNIV.difference(x0.join(gt));
        return x1.in(uptakelg).implies(x1.in(releaselg).not()).forAll(x0.oneOf(UNIV));
    }

    /**
     * Returns the sulfonylurea_effect axiom.
     *
     * @return sulfonylurea_effect
     */
    public final Formula sulfonylurea_effect() {
        final Variable x0 = Variable.unary("X0");
        final Expression x1 = UNIV.difference(x0.join(gt));
        return x1.in(drugi).and(x0.in(bcapacityex).not()).implies(x1.in(bsecretioni)).forAll(x0.oneOf(UNIV));
    }

    /**
     * Returns the biguanide_effect axiom.
     *
     * @return biguanide_effect
     */
    public final Formula biguanide_effect() {
        final Variable x0 = Variable.unary("X0");
        final Expression x1 = UNIV.difference(x0.join(gt));
        return x1.in(drugbg).implies(x1.in(releaselg).not()).forAll(x0.oneOf(UNIV));
    }

    /**
     * Returns the sn_cure_1 axiom.
     *
     * @return sn_cure_1
     */
    public final Formula sn_cure_1() {
        final Variable x0 = Variable.unary("X0");
        final Expression x1 = UNIV.difference(x0.join(gt));
        final Formula f0 = x1.in(bsecretioni).and(x0.in(bcapacitysn)).and(x0.in(qilt27)).and(x0.join(gt).in(conditionhyper));
        return f0.implies(x1.in(conditionnormo)).forAll(x0.oneOf(UNIV));
    }

    /**
     * Returns the sn_cure_2 axiom.
     *
     * @return sn_cure_2
     */
    public final Formula sn_cure_2() {
        final Variable x0 = Variable.unary("X0");
        final Expression x1 = UNIV.difference(x0.join(gt));
        final Formula f0 = x1.in(releaselg).not().and(x0.in(bcapacitysn)).and(x0.in(qilt27).not()).and(x0.join(gt).in(conditionhyper));
        return f0.implies(x1.in(conditionnormo)).forAll(x0.oneOf(UNIV));
    }

    /**
     * Returns the ne_cure axiom.
     *
     * @return ne_cure
     */
    public final Formula ne_cure() {
        final Variable x0 = Variable.unary("X0");
        final Expression x1 = UNIV.difference(x0.join(gt));
        final Formula f0 = x1.in(releaselg).not().or(x1.in(uptakepg)).and(x0.in(bcapacityne)).and(x1.in(bsecretioni)).and(x0.join(gt).in(conditionhyper));
        return f0.implies(x1.in(conditionnormo)).forAll(x0.oneOf(UNIV));
    }

    /**
     * Returns the ex_cure axiom.
     *
     * @return ex_cure
     */
    public final Formula ex_cure() {
        final Variable x0 = Variable.unary("X0");
        final Expression x1 = UNIV.difference(x0.join(gt));
        final Formula f0 = x1.in(uptakelg).and(x1.in(uptakepg)).and(x0.in(bcapacityex).not()).and(x0.join(gt).in(conditionhyper));
        return f0.implies(x1.in(conditionnormo.union(conditionhypo))).forAll(x0.oneOf(UNIV));
    }

    /**
     * Returns the axioms xorstep1 through xorstep7.
     *
     * @return xorstep1_7
     */
    public final Formula xorstep1_7() {
        return UNIV.in(s0.union(s1).union(s2).union(s3)).and(s0.intersection(s1).no()).and(s0.intersection(s2).no()).and(s0.intersection(s3).no()).and(s1.intersection(s2).no()).and(s1.intersection(s3).no()).and(s2.intersection(s3).no());
    }

    /**
     * Returns the normo axiom.
     *
     * @return normo
     */
    public final Formula normo() {
        final Variable x0 = Variable.unary("X0");
        final Expression x1 = UNIV.difference(x0.join(gt));
        final Formula f0 = x1.in(bsecretioni).and(x0.in(bcapacitysn)).and(x0.in(qilt27)).and(x0.join(gt).in(conditionhyper));
        final Formula f1 = x1.in(releaselg).not().and(x0.in(bcapacitysn)).and(x0.in(qilt27).not()).and(x0.join(gt).in(conditionhyper));
        final Formula f2 = x1.in(releaselg).not().or(x1.in(uptakelg)).and(x0.in(bcapacitysn)).and(x1.in(bsecretioni)).and(x0.join(gt).in(conditionhyper));
        final Formula f3 = x1.in(uptakelg).and(x1.in(uptakepg)).and(x0.in(bcapacityex)).and(x0.join(gt).in(conditionhyper));
        return x1.in(conditionnormo).implies(f0.or(f1).or(f2).or(f3)).forAll(x0.oneOf(UNIV));
    }

    /**
     * Returns the axioms step1 through step4.
     *
     * @return step1_4
     */
    public final Formula step1_4() {
        return s1.intersection(qilt27).in(drugsu).and(s1.intersection(UNIV.difference(qilt27)).in(drugbg)).and(s2.in(drugbg.intersection(drugsu))).and(s3.in(drugi.intersection(drugsu.union(drugbg)).union(drugi)));
    }

    /**
     * Returns the axioms sucomp and insulincomp.
     *
     * @return *comp
     */
    public final Formula comp() {
        return drugsu.in(s1.intersection(qilt27).union(s2).union(s3)).and(drugi.in(s3));
    }

    /**
     * Returns the insulin_completion axiom.
     *
     * @return insulin_completion
     */
    public final Formula insulin_completion() {
        final Variable x0 = Variable.unary("X0");
        final Expression x1 = UNIV.difference(x0.join(gt));
        final Formula f0 = x1.in(uptakelg.union(uptakepg));
        return f0.implies(x1.in(drugi)).forAll(x0.oneOf(UNIV));
    }

    /**
     * Returns the uptake_completion axiom.
     *
     * @return uptake_completion
     */
    public final Formula uptake_completion() {
        final Variable x0 = Variable.unary("X0");
        final Expression x1 = UNIV.difference(x0.join(gt));
        final Formula f0 = x1.in(releaselg).not();
        return f0.implies(x1.in(uptakelg)).forAll(x0.oneOf(UNIV));
    }

    /**
     * Returns the su_completion axiom.
     *
     * @return su_completion
     */
    public final Formula su_completion() {
        final Variable x0 = Variable.unary("X0");
        final Expression x1 = UNIV.difference(x0.join(gt));
        final Formula f0 = x1.in(bsecretioni);
        return f0.implies(x1.in(drugsu).and(x0.in(bcapacityex).not())).forAll(x0.oneOf(UNIV));
    }

    /**
     * Returns the bg_completion axiom.
     *
     * @return bg_completion
     */
    public final Formula bg_completion() {
        final Variable x0 = Variable.unary("X0");
        final Expression x1 = UNIV.difference(x0.join(gt));
        final Formula f0 = x1.in(releaselg).not();
        return f0.implies(x1.in(drugbg)).forAll(x0.oneOf(UNIV));
    }

    /**
     * Returns the trans_ax1 axiom.
     *
     * @return trans_ax1
     */
    public final Formula trans_ax1() {
        final Variable x0 = Variable.unary("X0");
        final Expression x1 = UNIV.difference(x0.join(gt));
        final Formula f0 = x0.in(s0).and(x1.in(conditionnormo).not());
        final Formula f1 = x1.intersection(s1).some().and(x1.join(gt).in(conditionhyper));
        return f0.implies(f1).forAll(x0.oneOf(UNIV));
    }

    /**
     * Returns the trans_ax2 axiom.
     *
     * @return trans_ax2
     */
    public final Formula trans_ax2() {
        final Variable x0 = Variable.unary("X0");
        final Expression x1 = UNIV.difference(x0.join(gt));
        final Formula f0 = x0.in(s1).and(x1.in(conditionnormo).not());
        final Formula f1 = x1.intersection(s2).intersection(bcapacityne.union(bcapacityex)).some().and(x1.join(gt).in(conditionhyper));
        return f0.implies(f1).forAll(x0.oneOf(UNIV));
    }

    /**
     * Returns the trans_ax3 axiom.
     *
     * @return trans_ax3
     */
    public final Formula trans_ax3() {
        final Variable x0 = Variable.unary("X0");
        final Expression x1 = UNIV.difference(x0.join(gt));
        final Formula f0 = x0.in(s2).and(x1.in(conditionnormo).not());
        final Formula f1 = x1.intersection(s3).intersection(bcapacityex).some().and(x1.join(gt).in(conditionhyper));
        return f0.implies(f1).forAll(x0.oneOf(UNIV));
    }

    /**
     * Returns the conjunction of all axioms.
     *
     * @return conjunction of all axioms.
     */
    public final Formula axioms() {
        return Formula.and(trans_ax2(), trans_ax3(), transitivity_gt(), decls(), irreflexivity_gt(), normo(), xorcapacity1_4(), xorcondition1_4(), insulin_effect(), liver_glucose(), sulfonylurea_effect(), biguanide_effect(), bg_completion(), sn_cure_1(), sn_cure_2(), ne_cure(), ex_cure(), su_completion(), xorstep1_7(), step1_4(), comp(), insulin_completion(), uptake_completion(), trans_ax1());
    }

    /**
     * Returns bounds for the given scope.
     *
     * @return bounds for the given scope.
     */
    public final Bounds bounds(int n) {
        assert n > 0;
        final List<String> atoms = new ArrayList<String>(n);
        for (int i = 0; i < n; i++)
            atoms.add("a" + i);
        final Universe u = new Universe(atoms);
        final Bounds b = new Bounds(u);
        final TupleFactory f = u.factory();
        final TupleSet s = f.allOf(1);
        b.bound(bcapacityne, s);
        b.bound(bcapacityex, s);
        b.bound(bcapacitysn, s);
        b.bound(conditionhyper, s);
        b.bound(conditionhypo, s);
        b.bound(conditionnormo, s);
        b.bound(drugi, s);
        b.bound(uptakelg, s);
        b.bound(uptakepg, s);
        b.bound(releaselg, s);
        b.bound(bsecretioni, s);
        b.bound(drugbg, s);
        b.bound(qilt27, s);
        b.bound(s0, s);
        b.bound(s1, s);
        b.bound(s2, s);
        b.bound(s3, s);
        b.bound(drugsu, s);
        b.bound(n0, s);
        b.bound(gt, f.allOf(2));
        return b;
    }
}
