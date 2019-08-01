// Generated from Smt.g4 by ANTLR 4.7.2
package edu.uiowa.smt.parser.antlr;
import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * This interface defines a complete generic visitor for a parse tree produced
 * by {@link SmtParser}.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public interface SmtVisitor<T> extends ParseTreeVisitor<T> {
	/**
	 * Visit a parse tree produced by {@link SmtParser#model}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitModel(SmtParser.ModelContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#sortDeclaration}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSortDeclaration(SmtParser.SortDeclarationContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#functionDefinition}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFunctionDefinition(SmtParser.FunctionDefinitionContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#argument}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitArgument(SmtParser.ArgumentContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#sort}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSort(SmtParser.SortContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#setSort}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSetSort(SmtParser.SetSortContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#tupleSort}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTupleSort(SmtParser.TupleSortContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#sortName}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSortName(SmtParser.SortNameContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#arity}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitArity(SmtParser.ArityContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#functionName}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFunctionName(SmtParser.FunctionNameContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#argumentName}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitArgumentName(SmtParser.ArgumentNameContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitExpression(SmtParser.ExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#unaryExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitUnaryExpression(SmtParser.UnaryExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#binaryExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBinaryExpression(SmtParser.BinaryExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#ternaryExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTernaryExpression(SmtParser.TernaryExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#multiArityExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMultiArityExpression(SmtParser.MultiArityExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#variable}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitVariable(SmtParser.VariableContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#constant}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitConstant(SmtParser.ConstantContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#boolConstant}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBoolConstant(SmtParser.BoolConstantContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#integerConstant}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIntegerConstant(SmtParser.IntegerConstantContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#uninterpretedConstant}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitUninterpretedConstant(SmtParser.UninterpretedConstantContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#emptySet}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitEmptySet(SmtParser.EmptySetContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#getValue}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGetValue(SmtParser.GetValueContext ctx);
}