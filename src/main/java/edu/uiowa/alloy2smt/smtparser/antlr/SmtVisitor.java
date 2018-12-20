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
	 * Visit a parse tree produced by {@link SmtParser#declarations}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDeclarations(SmtParser.DeclarationsContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#definitions}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDefinitions(SmtParser.DefinitionsContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#arguments}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitArguments(SmtParser.ArgumentsContext ctx);
	/**
	 * Visit a parse tree produced by {@link SmtParser#sort}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSort(SmtParser.SortContext ctx);
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
}