// Generated from Smt.g4 by ANTLR 4.7.2
package edu.uiowa.smt.parser.antlr;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class SmtParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.7.2", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		T__0=1, T__1=2, T__2=3, T__3=4, T__4=5, T__5=6, T__6=7, T__7=8, T__8=9, 
		T__9=10, True=11, False=12, UnaryOperator=13, BinaryOperator=14, TernaryOperator=15, 
		MultiArityOperator=16, AtomPrefix=17, UninterpretedIntPrefix=18, Identifier=19, 
		IdentifierLetter=20, Integer=21, Digit=22, Comment=23, Whitespace=24;
	public static final int
		RULE_model = 0, RULE_sortDeclaration = 1, RULE_functionDefinition = 2, 
		RULE_argument = 3, RULE_sort = 4, RULE_setSort = 5, RULE_tupleSort = 6, 
		RULE_sortName = 7, RULE_arity = 8, RULE_functionName = 9, RULE_argumentName = 10, 
		RULE_expression = 11, RULE_unaryExpression = 12, RULE_binaryExpression = 13, 
		RULE_ternaryExpression = 14, RULE_multiArityExpression = 15, RULE_variable = 16, 
		RULE_constant = 17, RULE_boolConstant = 18, RULE_integerConstant = 19, 
		RULE_uninterpretedConstant = 20, RULE_emptySet = 21, RULE_getValue = 22;
	private static String[] makeRuleNames() {
		return new String[] {
			"model", "sortDeclaration", "functionDefinition", "argument", "sort", 
			"setSort", "tupleSort", "sortName", "arity", "functionName", "argumentName", 
			"expression", "unaryExpression", "binaryExpression", "ternaryExpression", 
			"multiArityExpression", "variable", "constant", "boolConstant", "integerConstant", 
			"uninterpretedConstant", "emptySet", "getValue"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'('", "'model'", "')'", "'declare-sort'", "'define-fun'", "'Set'", 
			"'Tuple'", "'-'", "'as'", "'emptyset'", "'true'", "'false'", null, null, 
			"'ite'", null, "'@uc_Atom_'", "'@uc_UninterpretedInt_'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, null, null, null, null, null, null, null, null, null, null, "True", 
			"False", "UnaryOperator", "BinaryOperator", "TernaryOperator", "MultiArityOperator", 
			"AtomPrefix", "UninterpretedIntPrefix", "Identifier", "IdentifierLetter", 
			"Integer", "Digit", "Comment", "Whitespace"
		};
	}
	private static final String[] _SYMBOLIC_NAMES = makeSymbolicNames();
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}

	@Override
	public String getGrammarFileName() { return "Smt.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }

	public SmtParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	public static class ModelContext extends ParserRuleContext {
		public List<SortDeclarationContext> sortDeclaration() {
			return getRuleContexts(SortDeclarationContext.class);
		}
		public SortDeclarationContext sortDeclaration(int i) {
			return getRuleContext(SortDeclarationContext.class,i);
		}
		public List<FunctionDefinitionContext> functionDefinition() {
			return getRuleContexts(FunctionDefinitionContext.class);
		}
		public FunctionDefinitionContext functionDefinition(int i) {
			return getRuleContext(FunctionDefinitionContext.class,i);
		}
		public ModelContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_model; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterModel(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitModel(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitModel(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ModelContext model() throws RecognitionException {
		ModelContext _localctx = new ModelContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_model);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(46);
			match(T__0);
			setState(47);
			match(T__1);
			setState(51);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,0,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					{
					{
					setState(48);
					sortDeclaration();
					}
					} 
				}
				setState(53);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,0,_ctx);
			}
			setState(57);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__0) {
				{
				{
				setState(54);
				functionDefinition();
				}
				}
				setState(59);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(60);
			match(T__2);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class SortDeclarationContext extends ParserRuleContext {
		public SortNameContext sortName() {
			return getRuleContext(SortNameContext.class,0);
		}
		public ArityContext arity() {
			return getRuleContext(ArityContext.class,0);
		}
		public SortDeclarationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_sortDeclaration; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterSortDeclaration(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitSortDeclaration(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitSortDeclaration(this);
			else return visitor.visitChildren(this);
		}
	}

	public final SortDeclarationContext sortDeclaration() throws RecognitionException {
		SortDeclarationContext _localctx = new SortDeclarationContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_sortDeclaration);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(62);
			match(T__0);
			setState(63);
			match(T__3);
			setState(64);
			sortName();
			setState(65);
			arity();
			setState(66);
			match(T__2);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class FunctionDefinitionContext extends ParserRuleContext {
		public FunctionNameContext functionName() {
			return getRuleContext(FunctionNameContext.class,0);
		}
		public SortContext sort() {
			return getRuleContext(SortContext.class,0);
		}
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public List<ArgumentContext> argument() {
			return getRuleContexts(ArgumentContext.class);
		}
		public ArgumentContext argument(int i) {
			return getRuleContext(ArgumentContext.class,i);
		}
		public FunctionDefinitionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_functionDefinition; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterFunctionDefinition(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitFunctionDefinition(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitFunctionDefinition(this);
			else return visitor.visitChildren(this);
		}
	}

	public final FunctionDefinitionContext functionDefinition() throws RecognitionException {
		FunctionDefinitionContext _localctx = new FunctionDefinitionContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_functionDefinition);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(68);
			match(T__0);
			setState(69);
			match(T__4);
			setState(70);
			functionName();
			setState(71);
			match(T__0);
			setState(75);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__0) {
				{
				{
				setState(72);
				argument();
				}
				}
				setState(77);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(78);
			match(T__2);
			setState(79);
			sort();
			setState(80);
			expression();
			setState(81);
			match(T__2);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ArgumentContext extends ParserRuleContext {
		public ArgumentNameContext argumentName() {
			return getRuleContext(ArgumentNameContext.class,0);
		}
		public SortContext sort() {
			return getRuleContext(SortContext.class,0);
		}
		public ArgumentContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_argument; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterArgument(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitArgument(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitArgument(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ArgumentContext argument() throws RecognitionException {
		ArgumentContext _localctx = new ArgumentContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_argument);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(83);
			match(T__0);
			setState(84);
			argumentName();
			setState(85);
			sort();
			setState(86);
			match(T__2);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class SortContext extends ParserRuleContext {
		public SortNameContext sortName() {
			return getRuleContext(SortNameContext.class,0);
		}
		public TupleSortContext tupleSort() {
			return getRuleContext(TupleSortContext.class,0);
		}
		public SetSortContext setSort() {
			return getRuleContext(SetSortContext.class,0);
		}
		public SortContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_sort; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterSort(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitSort(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitSort(this);
			else return visitor.visitChildren(this);
		}
	}

	public final SortContext sort() throws RecognitionException {
		SortContext _localctx = new SortContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_sort);
		try {
			setState(97);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,3,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(88);
				sortName();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(89);
				match(T__0);
				setState(90);
				tupleSort();
				setState(91);
				match(T__2);
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(93);
				match(T__0);
				setState(94);
				setSort();
				setState(95);
				match(T__2);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class SetSortContext extends ParserRuleContext {
		public SortContext sort() {
			return getRuleContext(SortContext.class,0);
		}
		public SetSortContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_setSort; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterSetSort(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitSetSort(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitSetSort(this);
			else return visitor.visitChildren(this);
		}
	}

	public final SetSortContext setSort() throws RecognitionException {
		SetSortContext _localctx = new SetSortContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_setSort);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(99);
			match(T__5);
			setState(100);
			sort();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class TupleSortContext extends ParserRuleContext {
		public List<SortContext> sort() {
			return getRuleContexts(SortContext.class);
		}
		public SortContext sort(int i) {
			return getRuleContext(SortContext.class,i);
		}
		public TupleSortContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_tupleSort; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterTupleSort(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitTupleSort(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitTupleSort(this);
			else return visitor.visitChildren(this);
		}
	}

	public final TupleSortContext tupleSort() throws RecognitionException {
		TupleSortContext _localctx = new TupleSortContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_tupleSort);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(102);
			match(T__6);
			setState(104); 
			_errHandler.sync(this);
			_la = _input.LA(1);
			do {
				{
				{
				setState(103);
				sort();
				}
				}
				setState(106); 
				_errHandler.sync(this);
				_la = _input.LA(1);
			} while ( _la==T__0 || _la==Identifier );
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class SortNameContext extends ParserRuleContext {
		public TerminalNode Identifier() { return getToken(SmtParser.Identifier, 0); }
		public SortNameContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_sortName; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterSortName(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitSortName(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitSortName(this);
			else return visitor.visitChildren(this);
		}
	}

	public final SortNameContext sortName() throws RecognitionException {
		SortNameContext _localctx = new SortNameContext(_ctx, getState());
		enterRule(_localctx, 14, RULE_sortName);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(108);
			match(Identifier);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ArityContext extends ParserRuleContext {
		public TerminalNode Integer() { return getToken(SmtParser.Integer, 0); }
		public ArityContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_arity; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterArity(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitArity(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitArity(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ArityContext arity() throws RecognitionException {
		ArityContext _localctx = new ArityContext(_ctx, getState());
		enterRule(_localctx, 16, RULE_arity);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(110);
			match(Integer);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class FunctionNameContext extends ParserRuleContext {
		public TerminalNode Identifier() { return getToken(SmtParser.Identifier, 0); }
		public FunctionNameContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_functionName; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterFunctionName(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitFunctionName(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitFunctionName(this);
			else return visitor.visitChildren(this);
		}
	}

	public final FunctionNameContext functionName() throws RecognitionException {
		FunctionNameContext _localctx = new FunctionNameContext(_ctx, getState());
		enterRule(_localctx, 18, RULE_functionName);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(112);
			match(Identifier);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ArgumentNameContext extends ParserRuleContext {
		public TerminalNode Identifier() { return getToken(SmtParser.Identifier, 0); }
		public ArgumentNameContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_argumentName; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterArgumentName(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitArgumentName(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitArgumentName(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ArgumentNameContext argumentName() throws RecognitionException {
		ArgumentNameContext _localctx = new ArgumentNameContext(_ctx, getState());
		enterRule(_localctx, 20, RULE_argumentName);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(114);
			match(Identifier);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExpressionContext extends ParserRuleContext {
		public ConstantContext constant() {
			return getRuleContext(ConstantContext.class,0);
		}
		public VariableContext variable() {
			return getRuleContext(VariableContext.class,0);
		}
		public UnaryExpressionContext unaryExpression() {
			return getRuleContext(UnaryExpressionContext.class,0);
		}
		public BinaryExpressionContext binaryExpression() {
			return getRuleContext(BinaryExpressionContext.class,0);
		}
		public TernaryExpressionContext ternaryExpression() {
			return getRuleContext(TernaryExpressionContext.class,0);
		}
		public MultiArityExpressionContext multiArityExpression() {
			return getRuleContext(MultiArityExpressionContext.class,0);
		}
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public ExpressionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expression; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitExpression(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ExpressionContext expression() throws RecognitionException {
		ExpressionContext _localctx = new ExpressionContext(_ctx, getState());
		enterRule(_localctx, 22, RULE_expression);
		try {
			setState(126);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__7:
			case T__8:
			case True:
			case False:
			case AtomPrefix:
			case UninterpretedIntPrefix:
			case Integer:
				enterOuterAlt(_localctx, 1);
				{
				setState(116);
				constant();
				}
				break;
			case Identifier:
				enterOuterAlt(_localctx, 2);
				{
				setState(117);
				variable();
				}
				break;
			case UnaryOperator:
				enterOuterAlt(_localctx, 3);
				{
				setState(118);
				unaryExpression();
				}
				break;
			case BinaryOperator:
				enterOuterAlt(_localctx, 4);
				{
				setState(119);
				binaryExpression();
				}
				break;
			case TernaryOperator:
				enterOuterAlt(_localctx, 5);
				{
				setState(120);
				ternaryExpression();
				}
				break;
			case MultiArityOperator:
				enterOuterAlt(_localctx, 6);
				{
				setState(121);
				multiArityExpression();
				}
				break;
			case T__0:
				enterOuterAlt(_localctx, 7);
				{
				setState(122);
				match(T__0);
				setState(123);
				expression();
				setState(124);
				match(T__2);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class UnaryExpressionContext extends ParserRuleContext {
		public TerminalNode UnaryOperator() { return getToken(SmtParser.UnaryOperator, 0); }
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public UnaryExpressionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_unaryExpression; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterUnaryExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitUnaryExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitUnaryExpression(this);
			else return visitor.visitChildren(this);
		}
	}

	public final UnaryExpressionContext unaryExpression() throws RecognitionException {
		UnaryExpressionContext _localctx = new UnaryExpressionContext(_ctx, getState());
		enterRule(_localctx, 24, RULE_unaryExpression);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(128);
			match(UnaryOperator);
			setState(129);
			expression();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class BinaryExpressionContext extends ParserRuleContext {
		public TerminalNode BinaryOperator() { return getToken(SmtParser.BinaryOperator, 0); }
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public BinaryExpressionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_binaryExpression; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterBinaryExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitBinaryExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitBinaryExpression(this);
			else return visitor.visitChildren(this);
		}
	}

	public final BinaryExpressionContext binaryExpression() throws RecognitionException {
		BinaryExpressionContext _localctx = new BinaryExpressionContext(_ctx, getState());
		enterRule(_localctx, 26, RULE_binaryExpression);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(131);
			match(BinaryOperator);
			setState(132);
			expression();
			setState(133);
			expression();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class TernaryExpressionContext extends ParserRuleContext {
		public TerminalNode TernaryOperator() { return getToken(SmtParser.TernaryOperator, 0); }
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public TernaryExpressionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_ternaryExpression; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterTernaryExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitTernaryExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitTernaryExpression(this);
			else return visitor.visitChildren(this);
		}
	}

	public final TernaryExpressionContext ternaryExpression() throws RecognitionException {
		TernaryExpressionContext _localctx = new TernaryExpressionContext(_ctx, getState());
		enterRule(_localctx, 28, RULE_ternaryExpression);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(135);
			match(TernaryOperator);
			setState(136);
			expression();
			setState(137);
			expression();
			setState(138);
			expression();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class MultiArityExpressionContext extends ParserRuleContext {
		public TerminalNode MultiArityOperator() { return getToken(SmtParser.MultiArityOperator, 0); }
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public MultiArityExpressionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_multiArityExpression; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterMultiArityExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitMultiArityExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitMultiArityExpression(this);
			else return visitor.visitChildren(this);
		}
	}

	public final MultiArityExpressionContext multiArityExpression() throws RecognitionException {
		MultiArityExpressionContext _localctx = new MultiArityExpressionContext(_ctx, getState());
		enterRule(_localctx, 30, RULE_multiArityExpression);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(140);
			match(MultiArityOperator);
			setState(142); 
			_errHandler.sync(this);
			_alt = 1;
			do {
				switch (_alt) {
				case 1:
					{
					{
					setState(141);
					expression();
					}
					}
					break;
				default:
					throw new NoViableAltException(this);
				}
				setState(144); 
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,6,_ctx);
			} while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER );
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class VariableContext extends ParserRuleContext {
		public TerminalNode Identifier() { return getToken(SmtParser.Identifier, 0); }
		public VariableContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_variable; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterVariable(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitVariable(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitVariable(this);
			else return visitor.visitChildren(this);
		}
	}

	public final VariableContext variable() throws RecognitionException {
		VariableContext _localctx = new VariableContext(_ctx, getState());
		enterRule(_localctx, 32, RULE_variable);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(146);
			match(Identifier);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ConstantContext extends ParserRuleContext {
		public BoolConstantContext boolConstant() {
			return getRuleContext(BoolConstantContext.class,0);
		}
		public IntegerConstantContext integerConstant() {
			return getRuleContext(IntegerConstantContext.class,0);
		}
		public UninterpretedConstantContext uninterpretedConstant() {
			return getRuleContext(UninterpretedConstantContext.class,0);
		}
		public EmptySetContext emptySet() {
			return getRuleContext(EmptySetContext.class,0);
		}
		public ConstantContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_constant; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterConstant(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitConstant(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitConstant(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ConstantContext constant() throws RecognitionException {
		ConstantContext _localctx = new ConstantContext(_ctx, getState());
		enterRule(_localctx, 34, RULE_constant);
		try {
			setState(152);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case True:
			case False:
				enterOuterAlt(_localctx, 1);
				{
				setState(148);
				boolConstant();
				}
				break;
			case T__7:
			case Integer:
				enterOuterAlt(_localctx, 2);
				{
				setState(149);
				integerConstant();
				}
				break;
			case AtomPrefix:
			case UninterpretedIntPrefix:
				enterOuterAlt(_localctx, 3);
				{
				setState(150);
				uninterpretedConstant();
				}
				break;
			case T__8:
				enterOuterAlt(_localctx, 4);
				{
				setState(151);
				emptySet();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class BoolConstantContext extends ParserRuleContext {
		public TerminalNode True() { return getToken(SmtParser.True, 0); }
		public TerminalNode False() { return getToken(SmtParser.False, 0); }
		public BoolConstantContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_boolConstant; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterBoolConstant(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitBoolConstant(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitBoolConstant(this);
			else return visitor.visitChildren(this);
		}
	}

	public final BoolConstantContext boolConstant() throws RecognitionException {
		BoolConstantContext _localctx = new BoolConstantContext(_ctx, getState());
		enterRule(_localctx, 36, RULE_boolConstant);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(154);
			_la = _input.LA(1);
			if ( !(_la==True || _la==False) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class IntegerConstantContext extends ParserRuleContext {
		public TerminalNode Integer() { return getToken(SmtParser.Integer, 0); }
		public IntegerConstantContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_integerConstant; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterIntegerConstant(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitIntegerConstant(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitIntegerConstant(this);
			else return visitor.visitChildren(this);
		}
	}

	public final IntegerConstantContext integerConstant() throws RecognitionException {
		IntegerConstantContext _localctx = new IntegerConstantContext(_ctx, getState());
		enterRule(_localctx, 38, RULE_integerConstant);
		try {
			setState(159);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__7:
				enterOuterAlt(_localctx, 1);
				{
				setState(156);
				match(T__7);
				setState(157);
				match(Integer);
				}
				break;
			case Integer:
				enterOuterAlt(_localctx, 2);
				{
				setState(158);
				match(Integer);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class UninterpretedConstantContext extends ParserRuleContext {
		public TerminalNode Integer() { return getToken(SmtParser.Integer, 0); }
		public TerminalNode AtomPrefix() { return getToken(SmtParser.AtomPrefix, 0); }
		public TerminalNode UninterpretedIntPrefix() { return getToken(SmtParser.UninterpretedIntPrefix, 0); }
		public UninterpretedConstantContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_uninterpretedConstant; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterUninterpretedConstant(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitUninterpretedConstant(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitUninterpretedConstant(this);
			else return visitor.visitChildren(this);
		}
	}

	public final UninterpretedConstantContext uninterpretedConstant() throws RecognitionException {
		UninterpretedConstantContext _localctx = new UninterpretedConstantContext(_ctx, getState());
		enterRule(_localctx, 40, RULE_uninterpretedConstant);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(161);
			_la = _input.LA(1);
			if ( !(_la==AtomPrefix || _la==UninterpretedIntPrefix) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
			setState(162);
			match(Integer);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class EmptySetContext extends ParserRuleContext {
		public SortContext sort() {
			return getRuleContext(SortContext.class,0);
		}
		public EmptySetContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_emptySet; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterEmptySet(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitEmptySet(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitEmptySet(this);
			else return visitor.visitChildren(this);
		}
	}

	public final EmptySetContext emptySet() throws RecognitionException {
		EmptySetContext _localctx = new EmptySetContext(_ctx, getState());
		enterRule(_localctx, 42, RULE_emptySet);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(164);
			match(T__8);
			setState(165);
			match(T__9);
			setState(166);
			match(T__0);
			setState(167);
			match(T__5);
			setState(168);
			sort();
			setState(169);
			match(T__2);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class GetValueContext extends ParserRuleContext {
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public GetValueContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_getValue; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterGetValue(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitGetValue(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitGetValue(this);
			else return visitor.visitChildren(this);
		}
	}

	public final GetValueContext getValue() throws RecognitionException {
		GetValueContext _localctx = new GetValueContext(_ctx, getState());
		enterRule(_localctx, 44, RULE_getValue);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(171);
			match(T__0);
			setState(177); 
			_errHandler.sync(this);
			_la = _input.LA(1);
			do {
				{
				{
				setState(172);
				match(T__0);
				setState(173);
				expression();
				setState(174);
				expression();
				setState(175);
				match(T__2);
				}
				}
				setState(179); 
				_errHandler.sync(this);
				_la = _input.LA(1);
			} while ( _la==T__0 );
			setState(181);
			match(T__2);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3\32\u00ba\4\2\t\2"+
		"\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13"+
		"\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22\t\22"+
		"\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\3\2\3\2\3"+
		"\2\7\2\64\n\2\f\2\16\2\67\13\2\3\2\7\2:\n\2\f\2\16\2=\13\2\3\2\3\2\3\3"+
		"\3\3\3\3\3\3\3\3\3\3\3\4\3\4\3\4\3\4\3\4\7\4L\n\4\f\4\16\4O\13\4\3\4\3"+
		"\4\3\4\3\4\3\4\3\5\3\5\3\5\3\5\3\5\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6"+
		"\5\6d\n\6\3\7\3\7\3\7\3\b\3\b\6\bk\n\b\r\b\16\bl\3\t\3\t\3\n\3\n\3\13"+
		"\3\13\3\f\3\f\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\5\r\u0081\n\r\3"+
		"\16\3\16\3\16\3\17\3\17\3\17\3\17\3\20\3\20\3\20\3\20\3\20\3\21\3\21\6"+
		"\21\u0091\n\21\r\21\16\21\u0092\3\22\3\22\3\23\3\23\3\23\3\23\5\23\u009b"+
		"\n\23\3\24\3\24\3\25\3\25\3\25\5\25\u00a2\n\25\3\26\3\26\3\26\3\27\3\27"+
		"\3\27\3\27\3\27\3\27\3\27\3\30\3\30\3\30\3\30\3\30\3\30\6\30\u00b4\n\30"+
		"\r\30\16\30\u00b5\3\30\3\30\3\30\2\2\31\2\4\6\b\n\f\16\20\22\24\26\30"+
		"\32\34\36 \"$&(*,.\2\4\3\2\r\16\3\2\23\24\2\u00b4\2\60\3\2\2\2\4@\3\2"+
		"\2\2\6F\3\2\2\2\bU\3\2\2\2\nc\3\2\2\2\fe\3\2\2\2\16h\3\2\2\2\20n\3\2\2"+
		"\2\22p\3\2\2\2\24r\3\2\2\2\26t\3\2\2\2\30\u0080\3\2\2\2\32\u0082\3\2\2"+
		"\2\34\u0085\3\2\2\2\36\u0089\3\2\2\2 \u008e\3\2\2\2\"\u0094\3\2\2\2$\u009a"+
		"\3\2\2\2&\u009c\3\2\2\2(\u00a1\3\2\2\2*\u00a3\3\2\2\2,\u00a6\3\2\2\2."+
		"\u00ad\3\2\2\2\60\61\7\3\2\2\61\65\7\4\2\2\62\64\5\4\3\2\63\62\3\2\2\2"+
		"\64\67\3\2\2\2\65\63\3\2\2\2\65\66\3\2\2\2\66;\3\2\2\2\67\65\3\2\2\28"+
		":\5\6\4\298\3\2\2\2:=\3\2\2\2;9\3\2\2\2;<\3\2\2\2<>\3\2\2\2=;\3\2\2\2"+
		">?\7\5\2\2?\3\3\2\2\2@A\7\3\2\2AB\7\6\2\2BC\5\20\t\2CD\5\22\n\2DE\7\5"+
		"\2\2E\5\3\2\2\2FG\7\3\2\2GH\7\7\2\2HI\5\24\13\2IM\7\3\2\2JL\5\b\5\2KJ"+
		"\3\2\2\2LO\3\2\2\2MK\3\2\2\2MN\3\2\2\2NP\3\2\2\2OM\3\2\2\2PQ\7\5\2\2Q"+
		"R\5\n\6\2RS\5\30\r\2ST\7\5\2\2T\7\3\2\2\2UV\7\3\2\2VW\5\26\f\2WX\5\n\6"+
		"\2XY\7\5\2\2Y\t\3\2\2\2Zd\5\20\t\2[\\\7\3\2\2\\]\5\16\b\2]^\7\5\2\2^d"+
		"\3\2\2\2_`\7\3\2\2`a\5\f\7\2ab\7\5\2\2bd\3\2\2\2cZ\3\2\2\2c[\3\2\2\2c"+
		"_\3\2\2\2d\13\3\2\2\2ef\7\b\2\2fg\5\n\6\2g\r\3\2\2\2hj\7\t\2\2ik\5\n\6"+
		"\2ji\3\2\2\2kl\3\2\2\2lj\3\2\2\2lm\3\2\2\2m\17\3\2\2\2no\7\25\2\2o\21"+
		"\3\2\2\2pq\7\27\2\2q\23\3\2\2\2rs\7\25\2\2s\25\3\2\2\2tu\7\25\2\2u\27"+
		"\3\2\2\2v\u0081\5$\23\2w\u0081\5\"\22\2x\u0081\5\32\16\2y\u0081\5\34\17"+
		"\2z\u0081\5\36\20\2{\u0081\5 \21\2|}\7\3\2\2}~\5\30\r\2~\177\7\5\2\2\177"+
		"\u0081\3\2\2\2\u0080v\3\2\2\2\u0080w\3\2\2\2\u0080x\3\2\2\2\u0080y\3\2"+
		"\2\2\u0080z\3\2\2\2\u0080{\3\2\2\2\u0080|\3\2\2\2\u0081\31\3\2\2\2\u0082"+
		"\u0083\7\17\2\2\u0083\u0084\5\30\r\2\u0084\33\3\2\2\2\u0085\u0086\7\20"+
		"\2\2\u0086\u0087\5\30\r\2\u0087\u0088\5\30\r\2\u0088\35\3\2\2\2\u0089"+
		"\u008a\7\21\2\2\u008a\u008b\5\30\r\2\u008b\u008c\5\30\r\2\u008c\u008d"+
		"\5\30\r\2\u008d\37\3\2\2\2\u008e\u0090\7\22\2\2\u008f\u0091\5\30\r\2\u0090"+
		"\u008f\3\2\2\2\u0091\u0092\3\2\2\2\u0092\u0090\3\2\2\2\u0092\u0093\3\2"+
		"\2\2\u0093!\3\2\2\2\u0094\u0095\7\25\2\2\u0095#\3\2\2\2\u0096\u009b\5"+
		"&\24\2\u0097\u009b\5(\25\2\u0098\u009b\5*\26\2\u0099\u009b\5,\27\2\u009a"+
		"\u0096\3\2\2\2\u009a\u0097\3\2\2\2\u009a\u0098\3\2\2\2\u009a\u0099\3\2"+
		"\2\2\u009b%\3\2\2\2\u009c\u009d\t\2\2\2\u009d\'\3\2\2\2\u009e\u009f\7"+
		"\n\2\2\u009f\u00a2\7\27\2\2\u00a0\u00a2\7\27\2\2\u00a1\u009e\3\2\2\2\u00a1"+
		"\u00a0\3\2\2\2\u00a2)\3\2\2\2\u00a3\u00a4\t\3\2\2\u00a4\u00a5\7\27\2\2"+
		"\u00a5+\3\2\2\2\u00a6\u00a7\7\13\2\2\u00a7\u00a8\7\f\2\2\u00a8\u00a9\7"+
		"\3\2\2\u00a9\u00aa\7\b\2\2\u00aa\u00ab\5\n\6\2\u00ab\u00ac\7\5\2\2\u00ac"+
		"-\3\2\2\2\u00ad\u00b3\7\3\2\2\u00ae\u00af\7\3\2\2\u00af\u00b0\5\30\r\2"+
		"\u00b0\u00b1\5\30\r\2\u00b1\u00b2\7\5\2\2\u00b2\u00b4\3\2\2\2\u00b3\u00ae"+
		"\3\2\2\2\u00b4\u00b5\3\2\2\2\u00b5\u00b3\3\2\2\2\u00b5\u00b6\3\2\2\2\u00b6"+
		"\u00b7\3\2\2\2\u00b7\u00b8\7\5\2\2\u00b8/\3\2\2\2\f\65;Mcl\u0080\u0092"+
		"\u009a\u00a1\u00b5";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}