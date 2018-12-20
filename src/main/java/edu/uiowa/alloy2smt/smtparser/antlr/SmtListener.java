// Generated from Smt.g4 by ANTLR 4.7.2
package edu.uiowa.alloy2smt.smtparser.antlr;
import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link SmtParser}.
 */
public interface SmtListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link SmtParser#model}.
	 * @param ctx the parse tree
	 */
	void enterModel(SmtParser.ModelContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#model}.
	 * @param ctx the parse tree
	 */
	void exitModel(SmtParser.ModelContext ctx);
	/**
	 * Enter a parse tree produced by {@link SmtParser#declarations}.
	 * @param ctx the parse tree
	 */
	void enterDeclarations(SmtParser.DeclarationsContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#declarations}.
	 * @param ctx the parse tree
	 */
	void exitDeclarations(SmtParser.DeclarationsContext ctx);
	/**
	 * Enter a parse tree produced by {@link SmtParser#definitions}.
	 * @param ctx the parse tree
	 */
	void enterDefinitions(SmtParser.DefinitionsContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#definitions}.
	 * @param ctx the parse tree
	 */
	void exitDefinitions(SmtParser.DefinitionsContext ctx);
	/**
	 * Enter a parse tree produced by {@link SmtParser#arguments}.
	 * @param ctx the parse tree
	 */
	void enterArguments(SmtParser.ArgumentsContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#arguments}.
	 * @param ctx the parse tree
	 */
	void exitArguments(SmtParser.ArgumentsContext ctx);
	/**
	 * Enter a parse tree produced by {@link SmtParser#sort}.
	 * @param ctx the parse tree
	 */
	void enterSort(SmtParser.SortContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#sort}.
	 * @param ctx the parse tree
	 */
	void exitSort(SmtParser.SortContext ctx);
	/**
	 * Enter a parse tree produced by {@link SmtParser#arity}.
	 * @param ctx the parse tree
	 */
	void enterArity(SmtParser.ArityContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#arity}.
	 * @param ctx the parse tree
	 */
	void exitArity(SmtParser.ArityContext ctx);
	/**
	 * Enter a parse tree produced by {@link SmtParser#functionName}.
	 * @param ctx the parse tree
	 */
	void enterFunctionName(SmtParser.FunctionNameContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#functionName}.
	 * @param ctx the parse tree
	 */
	void exitFunctionName(SmtParser.FunctionNameContext ctx);
	/**
	 * Enter a parse tree produced by {@link SmtParser#argumentName}.
	 * @param ctx the parse tree
	 */
	void enterArgumentName(SmtParser.ArgumentNameContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#argumentName}.
	 * @param ctx the parse tree
	 */
	void exitArgumentName(SmtParser.ArgumentNameContext ctx);
	/**
	 * Enter a parse tree produced by {@link SmtParser#term}.
	 * @param ctx the parse tree
	 */
	void enterTerm(SmtParser.TermContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#term}.
	 * @param ctx the parse tree
	 */
	void exitTerm(SmtParser.TermContext ctx);
}