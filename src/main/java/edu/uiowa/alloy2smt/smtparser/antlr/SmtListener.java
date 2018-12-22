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
	 * Enter a parse tree produced by {@link SmtParser#term}.
	 * @param ctx the parse tree
	 */
	void enterTerm(SmtParser.TermContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#term}.
	 * @param ctx the parse tree
	 */
	void exitTerm(SmtParser.TermContext ctx);
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
	 * Enter a parse tree produced by {@link SmtParser#tupleConstant}.
	 * @param ctx the parse tree
	 */
	void enterTupleConstant(SmtParser.TupleConstantContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#tupleConstant}.
	 * @param ctx the parse tree
	 */
	void exitTupleConstant(SmtParser.TupleConstantContext ctx);
	/**
	 * Enter a parse tree produced by {@link SmtParser#singletonConstant}.
	 * @param ctx the parse tree
	 */
	void enterSingletonConstant(SmtParser.SingletonConstantContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#singletonConstant}.
	 * @param ctx the parse tree
	 */
	void exitSingletonConstant(SmtParser.SingletonConstantContext ctx);
	/**
	 * Enter a parse tree produced by {@link SmtParser#unionConstant}.
	 * @param ctx the parse tree
	 */
	void enterUnionConstant(SmtParser.UnionConstantContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#unionConstant}.
	 * @param ctx the parse tree
	 */
	void exitUnionConstant(SmtParser.UnionConstantContext ctx);
	/**
	 * Enter a parse tree produced by {@link SmtParser#atomConstant}.
	 * @param ctx the parse tree
	 */
	void enterAtomConstant(SmtParser.AtomConstantContext ctx);
	/**
	 * Exit a parse tree produced by {@link SmtParser#atomConstant}.
	 * @param ctx the parse tree
	 */
	void exitAtomConstant(SmtParser.AtomConstantContext ctx);
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