package kodkod.ast;

import kodkod.ast.visitor.ReturnVisitor;
import kodkod.ast.visitor.VoidVisitor;

public class FixFormula extends Formula {

    private final Formula formula;
    private final Formula condition;

    public FixFormula(Formula formula, Formula condition) {
        if (formula == null || condition == null) {
            throw new NullPointerException("null arg");
        }
        this.formula = formula;
        this.condition = condition;
    }

    public Formula formula() {
        return formula;
    }

    public Formula condition() {
        return condition;
    }

    @Override
    public <E, F, D, I> F accept(ReturnVisitor<E,F,D,I> visitor) {
        return visitor.visit(this);
    }

    @Override
    public void accept(VoidVisitor visitor) {
        visitor.visit(this);
    }

    @Override
    public String toString() {
        return "(fix " + formula + " | " + condition + ")";
    }

}
