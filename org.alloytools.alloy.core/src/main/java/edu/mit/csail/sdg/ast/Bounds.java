package edu.mit.csail.sdg.ast;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.Pos;

/** Immutable; represents a partial instance block. */
public class Bounds extends Expr {

    /** The label for a partial instance block. */
    public final String                  label;

    /** The list of scopes for each entity inside a partial instance block. */
    public final ArrayList<CommandScope> scope;

    /** The appended fact of the partial instance block. */
    public final Expr                    fact;

    /**
     * Constructs an empty partial instance block
     */
    public Bounds(String label) {
        super(Pos.UNKNOWN, null);
        this.label = label;
        scope = new ArrayList<CommandScope>();
        fact = null;
    }

    /**
     * Constructs a partial instance block
     */
    public Bounds(Pos pos, String label, List<CommandScope> list) {
        super(pos, Type.FORMULA);
        this.label = label;
        this.scope = new ArrayList<CommandScope>(list);
        fact = null;
    }

    /**
     * Constructs a partial instance block with an appended fact
     */
    public Bounds(Pos pos, String label, List<CommandScope> list, Expr fact) {
        super(pos, Type.FORMULA);
        this.label = label;
        this.scope = new ArrayList<CommandScope>(list);
        this.fact = fact;
    }

    /** {@inheritDoc} */
    @Override
    public void toString(StringBuilder out, int indent) {
        if (indent < 0) {
            out.append(label);
        } else {
            for (int i = 0; i < indent; i++) {
                out.append(' ');
            }
            out.append("inst ").append(label);
            out.append(" with scope=[");
            out.append(scope.stream().map(Object::toString).collect(Collectors.joining(",")));
            out.append("]");
            out.append(" and fact=").append(fact).append('\n');
        }
    }

    /** {@inheritDoc} */
    @Override
    public <T> T accept(VisitReturn<T> visitor) throws Err {
        return visitor.visit(this);
    }

    /** {@inheritDoc} */
    @Override
    public Expr resolve(Type t, Collection<ErrorWarning> warnings) {
        return this;
    }

    /** {@inheritDoc} */
    @Override
    public int getDepth() {
        throw new UnsupportedOperationException();
    }

    /** {@inheritDoc} */
    @Override
    public String getHTML() {
        return "<b>inst</b> " + label;
    }

    /** {@inheritDoc} */
    @Override
    public List< ? extends Browsable> getSubnodes() {
        throw new UnsupportedOperationException();
    }
}
