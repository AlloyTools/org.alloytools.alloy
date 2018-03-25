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
import kodkod.ast.FixFormula;
import kodkod.ast.IfExpression;
import kodkod.ast.IfIntExpression;
import kodkod.ast.IntComparisonFormula;
import kodkod.ast.IntConstant;
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

public abstract class AspectReturnVisitor<E, F, D, I> implements ReturnVisitor<E,F,D,I> {

    protected final ReturnVisitor<E,F,D,I> visitor;

    public AspectReturnVisitor(ReturnVisitor<E,F,D,I> visitor) {
        this.visitor = visitor;
    }

    protected void start(Node n) {}

    protected <T> T end(Node n, T ans) {
        return ans;
    }

    @Override
    public D visit(Decls decls) {
        start(decls);
        return end(decls, visitor.visit(decls));
    }

    @Override
    public D visit(Decl decl) {
        start(decl);
        return end(decl, visitor.visit(decl));
    }

    @Override
    public E visit(Relation relation) {
        start(relation);
        return end(relation, visitor.visit(relation));
    }

    @Override
    public E visit(Variable variable) {
        start(variable);
        return end(variable, visitor.visit(variable));
    }

    @Override
    public E visit(ConstantExpression constExpr) {
        start(constExpr);
        return end(constExpr, visitor.visit(constExpr));
    }

    @Override
    public E visit(NaryExpression expr) {
        start(expr);
        return end(expr, visitor.visit(expr));
    }

    @Override
    public E visit(BinaryExpression binExpr) {
        start(binExpr);
        return end(binExpr, visitor.visit(binExpr));
    }

    @Override
    public E visit(UnaryExpression unaryExpr) {
        start(unaryExpr);
        return end(unaryExpr, visitor.visit(unaryExpr));
    }

    @Override
    public E visit(Comprehension comprehension) {
        start(comprehension);
        return end(comprehension, visitor.visit(comprehension));
    }

    @Override
    public E visit(IfExpression ifExpr) {
        start(ifExpr);
        return end(ifExpr, visitor.visit(ifExpr));
    }

    @Override
    public E visit(ProjectExpression project) {
        start(project);
        return end(project, visitor.visit(project));
    }

    @Override
    public E visit(IntToExprCast castExpr) {
        start(castExpr);
        return end(castExpr, visitor.visit(castExpr));
    }

    @Override
    public I visit(IntConstant intConst) {
        start(intConst);
        return end(intConst, visitor.visit(intConst));
    }

    @Override
    public I visit(IfIntExpression intExpr) {
        start(intExpr);
        return end(intExpr, visitor.visit(intExpr));
    }

    @Override
    public I visit(ExprToIntCast intExpr) {
        start(intExpr);
        return end(intExpr, visitor.visit(intExpr));
    }

    @Override
    public I visit(NaryIntExpression intExpr) {
        start(intExpr);
        return end(intExpr, visitor.visit(intExpr));
    }

    @Override
    public I visit(BinaryIntExpression intExpr) {
        start(intExpr);
        return end(intExpr, visitor.visit(intExpr));
    }

    @Override
    public I visit(UnaryIntExpression intExpr) {
        start(intExpr);
        return end(intExpr, visitor.visit(intExpr));
    }

    @Override
    public I visit(SumExpression intExpr) {
        start(intExpr);
        return end(intExpr, visitor.visit(intExpr));
    }

    @Override
    public F visit(IntComparisonFormula intComp) {
        start(intComp);
        return end(intComp, visitor.visit(intComp));
    }

    @Override
    public F visit(ConstantFormula constant) {
        start(constant);
        return end(constant, visitor.visit(constant));
    }

    @Override
    public F visit(QuantifiedFormula quantFormula) {
        start(quantFormula);
        return end(quantFormula, visitor.visit(quantFormula));
    }

    @Override
    public F visit(NaryFormula formula) {
        start(formula);
        return end(formula, visitor.visit(formula));
    }

    @Override
    public F visit(BinaryFormula binFormula) {
        start(binFormula);
        return end(binFormula, visitor.visit(binFormula));
    }

    @Override
    public F visit(NotFormula not) {
        start(not);
        return end(not, visitor.visit(not));
    }

    @Override
    public F visit(ComparisonFormula compFormula) {
        start(compFormula);
        return end(compFormula, visitor.visit(compFormula));
    }

    @Override
    public F visit(MultiplicityFormula multFormula) {
        start(multFormula);
        return end(multFormula, visitor.visit(multFormula));
    }

    @Override
    public F visit(RelationPredicate pred) {
        start(pred);
        return end(pred, visitor.visit(pred));
    }

    @Override
    public F visit(FixFormula fixFormula) {
        start(fixFormula);
        return end(fixFormula, visitor.visit(fixFormula));
    }

}
