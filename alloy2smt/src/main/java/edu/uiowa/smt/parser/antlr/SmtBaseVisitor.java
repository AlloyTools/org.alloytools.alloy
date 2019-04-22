// Generated from Smt.g4 by ANTLR 4.7.2
package edu.uiowa.smt.parser.antlr;
import org.antlr.v4.runtime.tree.AbstractParseTreeVisitor;

/**
 * This class provides an empty implementation of {@link SmtVisitor},
 * which can be extended to create a visitor which only needs to handle a subset
 * of the available methods.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public class SmtBaseVisitor<T> extends AbstractParseTreeVisitor<T> implements SmtVisitor<T> {
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the satResult of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public T visitModel(SmtParser.ModelContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the satResult of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public T visitSortDeclaration(SmtParser.SortDeclarationContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the satResult of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public T visitFunctionDefinition(SmtParser.FunctionDefinitionContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the satResult of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public T visitArgument(SmtParser.ArgumentContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the satResult of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public T visitSort(SmtParser.SortContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the satResult of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public T visitSetSort(SmtParser.SetSortContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the satResult of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public T visitTupleSort(SmtParser.TupleSortContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the satResult of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public T visitSortName(SmtParser.SortNameContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the satResult of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public T visitArity(SmtParser.ArityContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the satResult of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public T visitFunctionName(SmtParser.FunctionNameContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the satResult of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public T visitArgumentName(SmtParser.ArgumentNameContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the satResult of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public T visitExpression(SmtParser.ExpressionContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the satResult of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public T visitUnaryExpression(SmtParser.UnaryExpressionContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the satResult of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public T visitBinaryExpression(SmtParser.BinaryExpressionContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the satResult of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public T visitTernaryExpression(SmtParser.TernaryExpressionContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the satResult of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public T visitMultiArityExpression(SmtParser.MultiArityExpressionContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the satResult of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public T visitVariable(SmtParser.VariableContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the satResult of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public T visitConstant(SmtParser.ConstantContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the satResult of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public T visitIntegerConstant(SmtParser.IntegerConstantContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the satResult of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public T visitUninterpretedConstant(SmtParser.UninterpretedConstantContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the satResult of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public T visitEmptySet(SmtParser.EmptySetContext ctx) { return visitChildren(ctx); }
}