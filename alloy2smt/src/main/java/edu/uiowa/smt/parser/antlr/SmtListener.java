// Generated from Smt.g4 by ANTLR 4.7.2
package edu.uiowa.smt.parser.antlr;
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
	 * Enter a parse tree produced by {@link SmtParser#sortDeclaration}.
	 * @param ctx the parse tree
	 */
	void enterSortDeclaration(SmtParser.SortDeclarationContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#sortDeclaration}.
	 * @param ctx the parse tree
	 */
	void exitSortDeclaration(SmtParser.SortDeclarationContext ctx);
	/**
	 * Enter a parse tree produced by {@link SmtParser#functionDefinition}.
	 * @param ctx the parse tree
	 */
	void enterFunctionDefinition(SmtParser.FunctionDefinitionContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#functionDefinition}.
	 * @param ctx the parse tree
	 */
	void exitFunctionDefinition(SmtParser.FunctionDefinitionContext ctx);
	/**
	 * Enter a parse tree produced by {@link SmtParser#argument}.
	 * @param ctx the parse tree
	 */
	void enterArgument(SmtParser.ArgumentContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#argument}.
	 * @param ctx the parse tree
	 */
	void exitArgument(SmtParser.ArgumentContext ctx);
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
	 * Enter a parse tree produced by {@link SmtParser#setSort}.
	 * @param ctx the parse tree
	 */
	void enterSetSort(SmtParser.SetSortContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#setSort}.
	 * @param ctx the parse tree
	 */
	void exitSetSort(SmtParser.SetSortContext ctx);
	/**
	 * Enter a parse tree produced by {@link SmtParser#tupleSort}.
	 * @param ctx the parse tree
	 */
	void enterTupleSort(SmtParser.TupleSortContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#tupleSort}.
	 * @param ctx the parse tree
	 */
	void exitTupleSort(SmtParser.TupleSortContext ctx);
	/**
	 * Enter a parse tree produced by {@link SmtParser#sortName}.
	 * @param ctx the parse tree
	 */
	void enterSortName(SmtParser.SortNameContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#sortName}.
	 * @param ctx the parse tree
	 */
	void exitSortName(SmtParser.SortNameContext ctx);
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
	 * Enter a parse tree produced by {@link SmtParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpression(SmtParser.ExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpression(SmtParser.ExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link SmtParser#unaryExpression}.
	 * @param ctx the parse tree
	 */
	void enterUnaryExpression(SmtParser.UnaryExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#unaryExpression}.
	 * @param ctx the parse tree
	 */
	void exitUnaryExpression(SmtParser.UnaryExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link SmtParser#binaryExpression}.
	 * @param ctx the parse tree
	 */
	void enterBinaryExpression(SmtParser.BinaryExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#binaryExpression}.
	 * @param ctx the parse tree
	 */
	void exitBinaryExpression(SmtParser.BinaryExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link SmtParser#ternaryExpression}.
	 * @param ctx the parse tree
	 */
	void enterTernaryExpression(SmtParser.TernaryExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#ternaryExpression}.
	 * @param ctx the parse tree
	 */
	void exitTernaryExpression(SmtParser.TernaryExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link SmtParser#multiArityExpression}.
	 * @param ctx the parse tree
	 */
	void enterMultiArityExpression(SmtParser.MultiArityExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#multiArityExpression}.
	 * @param ctx the parse tree
	 */
	void exitMultiArityExpression(SmtParser.MultiArityExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link SmtParser#variable}.
	 * @param ctx the parse tree
	 */
	void enterVariable(SmtParser.VariableContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#variable}.
	 * @param ctx the parse tree
	 */
	void exitVariable(SmtParser.VariableContext ctx);
	/**
	 * Enter a parse tree produced by {@link SmtParser#constant}.
	 * @param ctx the parse tree
	 */
	void enterConstant(SmtParser.ConstantContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#constant}.
	 * @param ctx the parse tree
	 */
	void exitConstant(SmtParser.ConstantContext ctx);
	/**
	 * Enter a parse tree produced by {@link SmtParser#integerConstant}.
	 * @param ctx the parse tree
	 */
	void enterIntegerConstant(SmtParser.IntegerConstantContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#integerConstant}.
	 * @param ctx the parse tree
	 */
	void exitIntegerConstant(SmtParser.IntegerConstantContext ctx);
	/**
	 * Enter a parse tree produced by {@link SmtParser#uninterpretedConstant}.
	 * @param ctx the parse tree
	 */
	void enterUninterpretedConstant(SmtParser.UninterpretedConstantContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#uninterpretedConstant}.
	 * @param ctx the parse tree
	 */
	void exitUninterpretedConstant(SmtParser.UninterpretedConstantContext ctx);
	/**
	 * Enter a parse tree produced by {@link SmtParser#emptySet}.
	 * @param ctx the parse tree
	 */
	void enterEmptySet(SmtParser.EmptySetContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#emptySet}.
	 * @param ctx the parse tree
	 */
	void exitEmptySet(SmtParser.EmptySetContext ctx);
}