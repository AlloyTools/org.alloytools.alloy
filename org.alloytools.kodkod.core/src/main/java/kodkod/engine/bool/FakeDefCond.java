package kodkod.engine.bool;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import kodkod.ast.Variable;
import kodkod.engine.fol2sat.Environment;

public class FakeDefCond implements IDefCond {

    private final Set<Variable> vars = Collections.unmodifiableSet(new HashSet<Variable>());

    public BooleanValue getOverflow()             { return BooleanConstant.FALSE; }
    public BooleanValue getAccumOverflow()        { return BooleanConstant.FALSE; }
    public void setOverflows(BooleanValue of, BooleanValue accumOF)  {}


    public void addVar(Variable v)                 {}
    public void addVars(Collection<Variable> vars) {}
    public Set<Variable> vars()                    { return vars; }

    public void setOverflowFlag(boolean overflow) {}
    public boolean isOverflowFlag()               { return false; }



    public static BooleanValue merge(BooleanFactory factory, BooleanValue accum, IDefCond ... conds) {
        return BooleanConstant.FALSE;
    }

    public static BooleanValue merge(BooleanFactory factory, IDefCond ... conds) {
        return BooleanConstant.FALSE;
    }

    public static BooleanValue ensureDef(BooleanFactory factory, Environment<?, ?> env, BooleanValue value, IDefCond ... dcs) {
        return value;
    }
}
