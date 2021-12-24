package edu.mit.csail.sdg.ast;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.Pos;

public final class Assert extends Expr implements Clause {
    public final Expr expr;
    public final Pos labelPos;
    public final String label;
    
    public Assert(Pos pos, Pos labelPos, String label, Expr expr) {
        super(pos, Type.FORMULA);
        this.expr = expr;
        this.labelPos = labelPos;
        this.label = label;
    }

    @Override
    public String explain() {
        return "assert " + label;
    }

    @Override
    public void toString(StringBuilder out, int indent) {
        if (indent < 0) {
            out.append(label);
        } else {
            for (int i = 0; i < indent; i++) {
                out.append(' ');
            }
            out.append( "assert ").append(label).append('\n');
        }
    }

    @Override
    public <T> T accept(VisitReturn<T> visitor) throws Err {
        return visitor.visit(this);
    }

    @Override
    public Expr resolve(Type t, Collection<ErrorWarning> warnings) {
        return this;
    }

    @Override
    public int getDepth() {
        return 1;
    }

    @Override
    public String getHTML() {
        return "<b>assert</b> " + label;
    }

    @Override
    public List< ? extends Browsable> getSubnodes() {
        return Arrays.asList(expr);
    }
}