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
package kodkod.ast.visitor;

import kodkod.ast.BinaryExpression;
import kodkod.ast.BinaryFormula;
import kodkod.ast.BinaryIntExpression;
import kodkod.ast.ComparisonFormula;
import kodkod.ast.Comprehension;
import kodkod.ast.ConstantExpression;
import kodkod.ast.ConstantFormula;
import kodkod.ast.Decl;
import kodkod.ast.Decls;
import kodkod.ast.ExprToIntCast;
import kodkod.ast.Expression;
import kodkod.ast.FixFormula;
import kodkod.ast.Formula;
import kodkod.ast.IfExpression;
import kodkod.ast.IfIntExpression;
import kodkod.ast.IntComparisonFormula;
import kodkod.ast.IntConstant;
import kodkod.ast.IntExpression;
import kodkod.ast.IntToExprCast;
import kodkod.ast.MultiplicityFormula;
import kodkod.ast.NaryExpression;
import kodkod.ast.NaryFormula;
import kodkod.ast.NaryIntExpression;
import kodkod.ast.Node;
import kodkod.ast.NotFormula;
import kodkod.ast.ProjectExpression;
import kodkod.ast.QuantifiedFormula;
import kodkod.ast.Relation;
import kodkod.ast.RelationPredicate;
import kodkod.ast.SumExpression;
import kodkod.ast.UnaryExpression;
import kodkod.ast.UnaryIntExpression;
import kodkod.ast.Variable;

/**
 * Implements a depth first traversal of the kodkod AST.
 *
 * @author Emina Torlak
 */
public abstract class AbstractVoidVisitor implements VoidVisitor {

    protected AbstractVoidVisitor() {}

    /**
     * Returns true if this node has already been visited. Otherwise returns false.
     *
     * @return true if this node has already been visited.
     */
    protected abstract boolean visited(Node n);

    /**
     * Visits all the children of the given declarations node if this.visited(decls)
     * returns false. Otherwise does nothing.
     *
     * @ensures all d: declarations.declarations | d.variable.accept(this) &&
     *          d.expression.accept(this)
     */
    @Override
    public void visit(Decls decls) {
        if (visited(decls))
            return;
        for (Decl decl : decls) {
            decl.accept(this);
        }
    }

    /**
     * Visits the variable and expression of this decl if this.visited(decl) returns
     * false. Otherwise does nothing.
     *
     * @ensures decl.variable.accept(this) && decl.expression.accept(this)
     */
    @Override
    public void visit(Decl decl) {
        if (visited(decl))
            return;
        decl.variable().accept(this);
        decl.expression().accept(this);
    }

    /**
     * Does nothing.
     */
    @Override
    public void visit(Relation relation) {}

    /**
     * Does nothing.
     */
    @Override
    public void visit(Variable variable) {}

    /**
     * Does nothing.
     */
    @Override
    public void visit(ConstantExpression constExpr) {}

    /**
     * Visits the children if this.visited(expr) returns false. Otherwise does
     * nothing.
     *
     * @ensures all i: [0..#expr.children) | expr.child(i).accept(this)
     */
    @Override
    public void visit(NaryExpression expr) {
        if (visited(expr))
            return;
        for (Expression child : expr) {
            child.accept(this);
        }
    }

    /**
     * Visits the left and right subexpressions if this.visited(binExpr) returns
     * false. Otherwise does nothing.
     *
     * @ensures binExpr.left.accept(this) && binExpr.right.accept(this)
     */
    @Override
    public void visit(BinaryExpression binExpr) {
        if (visited(binExpr))
            return;
        binExpr.left().accept(this);
        binExpr.right().accept(this);
    }

    /**
     * Visits the subexpression if this.visited(unaryExpr) returns false. Otherwise
     * does nothing.
     *
     * @ensures unaryExpr.expression.accept(this)
     */
    @Override
    public void visit(UnaryExpression unaryExpr) {
        if (visited(unaryExpr))
            return;
        unaryExpr.expression().accept(this);
    }

    /**
     * Visits the declarations and the formula if this.visited(comprehension)
     * returns false. Otherwise does nothing.
     *
     * @ensures comprehension.declarations.accept(this) &&
     *          comprehension.formula.accept(this)
     */
    @Override
    public void visit(Comprehension comprehension) {
        if (visited(comprehension))
            return;
        comprehension.decls().accept(this);
        comprehension.formula().accept(this);
    }

    /**
     * Visits the if-condition, the then-expression, and the else-expression if
     * this.visited(ifExpr) returns false. Otherwise does nothing.
     *
     * @ensures ifExpr.condition.accept(this) && ifExpr.thenExpr.accept(this) &&
     *          ifExpr.elseExpr.accept(this)
     */
    @Override
    public void visit(IfExpression ifExpr) {
        if (visited(ifExpr))
            return;
        ifExpr.condition().accept(this);
        ifExpr.thenExpr().accept(this);
        ifExpr.elseExpr().accept(this);
    }

    /**
     * Visits project.expression and project.columns if this.visited(project)
     * returns false. Otherwise does nothing.
     *
     * @ensures project.expression.accept(this) && all i: project.arity |
     *          project.columns[i].accept(this)
     */
    @Override
    public void visit(ProjectExpression project) {
        if (visited(project))
            return;
        project.expression().accept(this);
        for (int i = 0, arity = project.arity(); i < arity; i++) {
            project.column(i).accept(this);
        }
    }

    /**
     * Visits castExpr.intExpr if this.visited(castExpr) returns false. Otherwise
     * does nothing.
     *
     * @ensures castExpr.expression.accept(this)
     */
    @Override
    public void visit(IntToExprCast castExpr) {
        if (visited(castExpr))
            return;
        castExpr.intExpr().accept(this);
    }

    /**
     * Does nothing.
     */
    @Override
    public void visit(IntConstant intConst) {}

    /**
     * Visits the if-condition, the then-expression, and the else-expression if
     * this.visited(intExpr) returns false. Otherwise does nothing.
     *
     * @ensures intExpr.condition.accept(this) && intExpr.thenExpr.accept(this) &&
     *          intExpr.elseExpr.accept(this)
     */
    @Override
    public void visit(IfIntExpression intExpr) {
        if (visited(intExpr))
            return;
        intExpr.condition().accept(this);
        intExpr.thenExpr().accept(this);
        intExpr.elseExpr().accept(this);
    }

    /**
     * Visits intExpr.expression if this.visited(intExpr) returns false. Otherwise
     * does nothing.
     *
     * @ensures intExpr.expression.accept(this)
     */
    @Override
    public void visit(ExprToIntCast intExpr) {
        if (visited(intExpr))
            return;
        intExpr.expression().accept(this);
    }

    /**
     * Visits the children if this.visited(intExpr) returns false. Otherwise does
     * nothing.
     *
     * @ensures all i: [0..#intExpr.children) | intExpr.child(i).accept(this)
     */
    @Override
    public void visit(NaryIntExpression intExpr) {
        if (visited(intExpr))
            return;
        for (IntExpression child : intExpr) {
            child.accept(this);
        }
    }

    /**
     * Visits the children of the given integer expression if this.visited(intExpr)
     * returns false. Otherwise does nothing.
     *
     * @ensures intExpr.left.accept(this) && intExpr.right.accept(this)
     */
    @Override
    public void visit(BinaryIntExpression intExpr) {
        if (visited(intExpr))
            return;
        intExpr.left().accept(this);
        intExpr.right().accept(this);
    }

    /**
     * Visits the subexpression if this.visited(intExpr) returns false. Otherwise
     * does nothing.
     *
     * @ensures unaryExpr.expression.accept(this)
     */
    @Override
    public void visit(UnaryIntExpression intExpr) {
        if (visited(intExpr))
            return;
        intExpr.intExpr().accept(this);
    }

    /**
     * Visits the children of the given sum expression if this.visited(intExpr)
     * returns false. Otherwise does nothing.
     *
     * @ensures intExpr.decls.accept(this) && intExpr.intExpr.accept(this)
     */
    @Override
    public void visit(SumExpression intExpr) {
        if (visited(intExpr))
            return;
        intExpr.decls().accept(this);
        intExpr.intExpr().accept(this);
    }

    /**
     * Visits the children of the given integer comparison formula if
     * this.visited(intComp) returns false. Otherwise does nothing.
     *
     * @ensures intComp.left.accept(this) && intComp.right.accept(this)
     */
    @Override
    public void visit(IntComparisonFormula intComp) {
        if (visited(intComp))
            return;
        intComp.left().accept(this);
        intComp.right().accept(this);
    }

    /**
     * Visits the declarations and the formula if this.visited(quantFormula) returns
     * false. Otherwise does nothing.
     *
     * @ensures quantFormula.declarations.accept(this) &&
     *          quantFormula.formula.accept(this)
     */
    @Override
    public void visit(QuantifiedFormula quantFormula) {
        if (visited(quantFormula))
            return;
        quantFormula.decls().accept(this);
        quantFormula.formula().accept(this);
    }

    /**
     * Visits the children if this.visited(formula) returns false. Otherwise does
     * nothing.
     *
     * @ensures all i: [0..#formula.children) | formula.child(i).accept(this)
     */
    @Override
    public void visit(NaryFormula formula) {
        if (visited(formula))
            return;
        for (Formula child : formula) {
            child.accept(this);
        }
    }

    /**
     * Visits the left and right children if this.visited(binFormula) returns false.
     * Otherwise does nothing.
     *
     * @ensures binFormula.left.accept(this) && binFormula.right.accept(this)
     */
    @Override
    public void visit(BinaryFormula binFormula) {
        if (visited(binFormula))
            return;
        binFormula.left().accept(this);
        binFormula.right().accept(this);
    }

    /**
     * Visits the subformula if this.visited(not) returns false. Otherwise does
     * nothing.
     *
     * @ensures not.formula.accept(this)
     */
    @Override
    public void visit(NotFormula not) {
        if (visited(not))
            return;
        not.formula().accept(this);
    }

    /**
     * Does nothing.
     */
    @Override
    public void visit(ConstantFormula constant) {}

    /**
     * Visits the left and right children if this.visited(compFormula) returns
     * false. Otherwise does nothing.
     *
     * @ensures compFormula.left.accept(this) && compFormula.right.accept(this)
     */
    @Override
    public void visit(ComparisonFormula compFormula) {
        if (visited(compFormula))
            return;
        compFormula.left().accept(this);
        compFormula.right().accept(this);
    }

    /**
     * Visits the formula if this.visited(multFormula) returns false. Otherwise does
     * nothing.
     *
     * @ensures multFormula.expression.accept(this)
     */
    @Override
    public void visit(MultiplicityFormula multFormula) {
        if (visited(multFormula))
            return;
        multFormula.expression().accept(this);
    }

    /**
     * Visits the children of the predicate if this.visited(pred) returns false.
     * Otherwise does nothing.
     *
     * @ensures pred.relation.accept(this) && (pred.name = FUNCTION =>
     *          pred.domain.accept(this) && pred.range.accept(this)) && (pred.name =
     *          TOTAL_ORDERING => pred.ordered.accept(this) &&
     *          pred.first.accept(this) && pred.last.accept(this) )
     */
    @Override
    public void visit(RelationPredicate pred) {
        if (visited(pred))
            return;
        pred.relation().accept(this);
        if (pred.name() == RelationPredicate.Name.FUNCTION) {
            final RelationPredicate.Function fp = (RelationPredicate.Function) pred;
            fp.domain().accept(this);
            fp.range().accept(this);
        } else if (pred.name() == RelationPredicate.Name.TOTAL_ORDERING) {
            final RelationPredicate.TotalOrdering tp = (RelationPredicate.TotalOrdering) pred;
            tp.ordered().accept(this);
            tp.first().accept(this);
            tp.last().accept(this);
        }
    }

    @Override
    public void visit(FixFormula fixFormula) {
        if (visited(fixFormula))
            return;
        fixFormula.formula().accept(this);
        fixFormula.condition().accept(this);
    }

}
