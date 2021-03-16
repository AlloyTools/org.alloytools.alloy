package kodkod.engine.bool;

import java.util.Collection;
import java.util.Set;

import kodkod.ast.Variable;

public interface IDefCond {

    public BooleanValue getOverflow();

    public BooleanValue getAccumOverflow();

    public void setOverflows(BooleanValue of, BooleanValue accumOF);

    public void addVar(Variable v);

    public void addVars(Collection<Variable> vars);

    public Set<Variable> vars();
}
