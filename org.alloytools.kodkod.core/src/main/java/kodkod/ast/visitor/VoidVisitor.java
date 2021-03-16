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
 * A visitor that visits every node in the AST.
 *
 * @author Emina Torlak
 */
public interface VoidVisitor {

    /**
     * Visits the given sequence of declarations.
     **/
    public void visit(Decls decls);

    /**
     * Visits the given declaration.
     **/
    public void visit(Decl decl);

    /**
     * Visits the given relation.
     **/
    public void visit(Relation relation);

    /**
     * Visits the given variable.
     **/
    public void visit(Variable variable);

    /**
     * Visits the given constant expression.
     **/
    public void visit(ConstantExpression constExpr);

    /**
     * Visits the given unary expression.
     **/
    public void visit(UnaryExpression unaryExpr);

    /**
     * Visits the given binary expression.
     **/
    public void visit(BinaryExpression binExpr);

    /**
     * Visits the given nary expression.
     **/
    public void visit(NaryExpression expr);

    /**
     * Visits the given comprehension.
     **/
    public void visit(Comprehension comprehension);

    /**
     * Visits the given if-then expression.
     **/
    public void visit(IfExpression ifExpr);

    /**
     * Visits the given projection expression.
     */
    public void visit(ProjectExpression project);

    /**
     * Visits the given integer cast expression.
     */
    public void visit(IntToExprCast castExpr);

    /**
     * Visits the given integer constant.
     */
    public void visit(IntConstant intConst);

    /**
     * Visits the given unary integer expression.
     */
    public void visit(ExprToIntCast intExpr);

    /**
     * Visits the given if-int-expression.
     */
    public void visit(IfIntExpression intExpr);

    /**
     * Visits the given nary int expression.
     **/
    public void visit(NaryIntExpression intExpr);

    /**
     * Visits the given binary integer expression.
     */
    public void visit(BinaryIntExpression intExpr);

    /**
     * Visits the given unary integer expression.
     */
    public void visit(UnaryIntExpression intExpr);

    /**
     * Visits the given sum expression.
     */
    public void visit(SumExpression intExpr);

    /**
     * Visits the given integer comparison formula.
     */
    public void visit(IntComparisonFormula intComp);

    /**
     * Visits the given quantified formula.
     **/
    public void visit(QuantifiedFormula quantFormula);

    /**
     * Visits the given nary formula.
     **/
    public void visit(NaryFormula formula);

    /**
     * Visits the given binary formula.
     **/
    public void visit(BinaryFormula binFormula);

    /**
     * Visits the given negation.
     **/
    public void visit(NotFormula not);

    /**
     * Visits the given constant formula.
     **/
    public void visit(ConstantFormula constant);

    /**
     * Visits the given comparison formula.
     **/
    public void visit(ComparisonFormula compFormula);

    /**
     * Visits the given multiplicity formula.
     **/
    public void visit(MultiplicityFormula multFormula);

    /**
     * Visits the given relation predicate.
     */
    public void visit(RelationPredicate predicate);

    public void visit(FixFormula fixFormula);

}
