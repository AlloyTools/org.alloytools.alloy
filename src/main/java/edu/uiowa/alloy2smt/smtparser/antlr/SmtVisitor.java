// Generated from Smt.g4 by ANTLR 4.7.2
package edu.uiowa.alloy2smt.smtparser.antlr;
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
	 * Visit a parse tree produced by {@link SmtParser#term}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTerm(SmtParser.TermContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#integerConstant}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIntegerConstant(SmtParser.IntegerConstantContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#tupleConstant}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTupleConstant(SmtParser.TupleConstantContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#singletonConstant}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSingletonConstant(SmtParser.SingletonConstantContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#unionConstant}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitUnionConstant(SmtParser.UnionConstantContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#atomConstant}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAtomConstant(SmtParser.AtomConstantContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#emptySet}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitEmptySet(SmtParser.EmptySetContext ctx);
}