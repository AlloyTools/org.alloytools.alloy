package kodkod.engine.bool;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import kodkod.ast.Expression;
import kodkod.ast.Variable;
import kodkod.ast.operator.Quantifier;
import kodkod.engine.config.Options.OverflowPolicy;
import kodkod.engine.fol2sat.Environment;

public class DefCond implements IDefCond {

    /*
     * --------------------------------------------------------- ----------------
     * -----------
     */
    /* used during translation */
    /*
     * --------------------------------------------------------- ----------------
     * -----------
     */

    private BooleanValue  overflow      = BooleanConstant.FALSE;
    private BooleanValue  accumOverflow = BooleanConstant.FALSE;
    private Set<Variable> vars          = new HashSet<Variable>();

    @Override
    public BooleanValue getOverflow() {
        return overflow;
    }

    @Override
    public BooleanValue getAccumOverflow() {
        return accumOverflow;
    }

    @Override
    public void setOverflows(BooleanValue of, BooleanValue accumOF) {
        this.overflow = of;
        this.accumOverflow = accumOF;
    }

    @Override
    public void addVar(Variable v) {
        vars.add(v);
    }

    @Override
    public void addVars(Collection<Variable> vars) {
        this.vars.addAll(vars);
    }

    @Override
    public Set<Variable> vars() {
        return vars;
    }

    /**
     * ORs overflow circuits of <code>this</code> object (
     * <code>this.mergedOverflow</code>), a given <code>other</code> object (
     * <code>other.mergedOverflow</code>), and a given overflow circuit (
     * <code>of</code>)
     */
    public static BooleanValue merge(BooleanFactory factory, BooleanValue accum, IDefCond... conds) {
        BooleanValue ret = accum;
        for (IDefCond dc : conds) {
            ret = factory.or(ret, dc.getAccumOverflow());
        }
        return ret;
    }

    public static BooleanValue merge(BooleanFactory factory, IDefCond... conds) {
        return merge(factory, BooleanConstant.FALSE, conds);
    }

    /**
     * If overflow checking is disabled returns <code>value</code>. Otherwise,
     * returns a conjunction of <code>value</code>, <code>lhs.accumOverflow</code>,
     * and <code>rhs.accumOverflow</code>. ~~~ NOTE ~~~: Every time a BooleanValue
     * is returned as a result of an operation over Ints, one of the
     * <code>ensureNoOverflow</code> methods should be called.
     */
    public static BooleanValue ensureDef(BooleanFactory factory, Environment< ? , ? > env, BooleanValue value, IDefCond... dcs) {
        if (factory.noOverflow == OverflowPolicy.NONE)
            return value;
        List<IDefCond> univQuantInts = new ArrayList<IDefCond>(dcs.length);
        List<IDefCond> extQuantInts = new ArrayList<IDefCond>(dcs.length);
        for (IDefCond e : dcs) {
            if (isUnivQuant(env, e))
                univQuantInts.add(e);
            else
                extQuantInts.add(e);
        }
        BooleanValue ret = value;
        if ((!env.isNegated()) == (factory.noOverflow == OverflowPolicy.PREVENT)) {
            for (IDefCond e : univQuantInts)
                ret = factory.or(ret, e.getAccumOverflow());
            for (IDefCond e : extQuantInts)
                ret = factory.and(ret, factory.not(e.getAccumOverflow()));
        } else {
            for (IDefCond e : extQuantInts)
                ret = factory.or(ret, e.getAccumOverflow());
            for (IDefCond e : univQuantInts)
                ret = factory.and(ret, factory.not(e.getAccumOverflow()));
        }
        return ret;
    }

    private static boolean isUnivQuant(Environment< ? , ? > env, IDefCond e) {
        if (env.isEmpty())
            return false;
        if (!isInt(env.type()))
            return isUnivQuant(env.parent(), e);
        if (e.vars().contains(env.variable())) {
            return env.envType() == Quantifier.ALL;
        } else {
            return isUnivQuant(env.parent(), e);
        }
    }

    /**
     * Returns if this expression represents the Int type.
     */
    private static boolean isInt(Object expression) {
        if (expression == null)
            return false;
        if (!(expression instanceof Expression))
            return false;
        // TODO: this is probably not complete
        return "ints".equals(expression.toString());
    }

}
