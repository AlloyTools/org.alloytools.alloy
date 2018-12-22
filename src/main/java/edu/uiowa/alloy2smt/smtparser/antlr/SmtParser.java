// Generated from Smt.g4 by ANTLR 4.7.2
package edu.uiowa.alloy2smt.smtparser.antlr;
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
		T__9=10, T__10=11, T__11=12, T__12=13, T__13=14, Identifier=15, IdentifierLetter=16, 
		Integer=17, Digit=18, Comment=19, Whitespace=20;
	public static final int
		RULE_model = 0, RULE_sortDeclaration = 1, RULE_definition = 2, RULE_argument = 3, 
		RULE_sort = 4, RULE_setSort = 5, RULE_tupleSort = 6, RULE_sortName = 7, 
		RULE_arity = 8, RULE_functionName = 9, RULE_argumentName = 10, RULE_term = 11;
	private static String[] makeRuleNames() {
		return new String[] {
			"model", "sortDeclaration", "definition", "argument", "sort", "setSort", 
			"tupleSort", "sortName", "arity", "functionName", "argumentName", "term"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'('", "'model'", "')'", "'declare-sort'", "'define-fun'", "'Set'", 
			"'Tuple'", "'-'", "'mkTuple'", "'singleton'", "'union'", "'@uc_Atom_'", 
			"'as'", "'emptyset'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, "Identifier", "IdentifierLetter", "Integer", "Digit", 
			"Comment", "Whitespace"
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
		public List<DefinitionContext> definition() {
			return getRuleContexts(DefinitionContext.class);
		}
		public DefinitionContext definition(int i) {
			return getRuleContext(DefinitionContext.class,i);
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
			setState(24);
			match(T__0);
			setState(25);
			match(T__1);
			setState(29);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,0,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					{
					{
					setState(26);
					sortDeclaration();
					}
					} 
				}
				setState(31);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,0,_ctx);
			}
			setState(35);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__0) {
				{
				{
				setState(32);
				definition();
				}
				}
				setState(37);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(38);
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
			setState(40);
			match(T__0);
			setState(41);
			match(T__3);
			setState(42);
			sortName();
			setState(43);
			arity();
			setState(44);
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

	public static class DefinitionContext extends ParserRuleContext {
		public FunctionNameContext functionName() {
			return getRuleContext(FunctionNameContext.class,0);
		}
		public SortContext sort() {
			return getRuleContext(SortContext.class,0);
		}
		public TermContext term() {
			return getRuleContext(TermContext.class,0);
		}
		public List<ArgumentContext> argument() {
			return getRuleContexts(ArgumentContext.class);
		}
		public ArgumentContext argument(int i) {
			return getRuleContext(ArgumentContext.class,i);
		}
		public DefinitionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_definition; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterDefinition(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitDefinition(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitDefinition(this);
			else return visitor.visitChildren(this);
		}
	}

	public final DefinitionContext definition() throws RecognitionException {
		DefinitionContext _localctx = new DefinitionContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_definition);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(46);
			match(T__0);
			setState(47);
			match(T__4);
			setState(48);
			functionName();
			setState(49);
			match(T__0);
			setState(53);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__0) {
				{
				{
				setState(50);
				argument();
				}
				}
				setState(55);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(56);
			match(T__2);
			setState(57);
			match(T__0);
			setState(58);
			sort();
			setState(59);
			match(T__2);
			setState(60);
			match(T__0);
			setState(61);
			term();
			setState(62);
			match(T__2);
			setState(63);
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
			setState(65);
			match(T__0);
			setState(66);
			argumentName();
			setState(67);
			sort();
			setState(68);
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
			setState(73);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case Identifier:
				enterOuterAlt(_localctx, 1);
				{
				setState(70);
				sortName();
				}
				break;
			case T__6:
				enterOuterAlt(_localctx, 2);
				{
				setState(71);
				tupleSort();
				}
				break;
			case T__5:
				enterOuterAlt(_localctx, 3);
				{
				setState(72);
				setSort();
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
			setState(75);
			match(T__5);
			setState(76);
			match(T__0);
			setState(77);
			sort();
			setState(78);
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
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(80);
			match(T__6);
			setState(82); 
			_errHandler.sync(this);
			_alt = 1;
			do {
				switch (_alt) {
				case 1:
					{
					{
					setState(81);
					sort();
					}
					}
					break;
				default:
					throw new NoViableAltException(this);
				}
				setState(84); 
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,4,_ctx);
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
			setState(86);
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
			setState(88);
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
			setState(90);
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
			setState(92);
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

	public static class TermContext extends ParserRuleContext {
		public TerminalNode Integer() { return getToken(SmtParser.Integer, 0); }
		public List<TermContext> term() {
			return getRuleContexts(TermContext.class);
		}
		public TermContext term(int i) {
			return getRuleContext(TermContext.class,i);
		}
		public SortContext sort() {
			return getRuleContext(SortContext.class,0);
		}
		public TermContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_term; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterTerm(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitTerm(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitTerm(this);
			else return visitor.visitChildren(this);
		}
	}

	public final TermContext term() throws RecognitionException {
		TermContext _localctx = new TermContext(_ctx, getState());
		enterRule(_localctx, 22, RULE_term);
		int _la;
		try {
			int _alt;
			setState(128);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case Integer:
				enterOuterAlt(_localctx, 1);
				{
				setState(94);
				match(Integer);
				}
				break;
			case T__7:
				enterOuterAlt(_localctx, 2);
				{
				setState(95);
				match(T__7);
				setState(96);
				match(Integer);
				}
				break;
			case T__8:
				enterOuterAlt(_localctx, 3);
				{
				setState(97);
				match(T__8);
				setState(99); 
				_errHandler.sync(this);
				_alt = 1;
				do {
					switch (_alt) {
					case 1:
						{
						{
						setState(98);
						term();
						}
						}
						break;
					default:
						throw new NoViableAltException(this);
					}
					setState(101); 
					_errHandler.sync(this);
					_alt = getInterpreter().adaptivePredict(_input,5,_ctx);
				} while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER );
				}
				break;
			case T__9:
				enterOuterAlt(_localctx, 4);
				{
				setState(103);
				match(T__9);
				setState(104);
				match(T__0);
				setState(105);
				term();
				setState(106);
				match(T__2);
				}
				break;
			case T__10:
				enterOuterAlt(_localctx, 5);
				{
				setState(108);
				match(T__10);
				setState(113); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(109);
					match(T__0);
					setState(110);
					term();
					setState(111);
					match(T__2);
					}
					}
					setState(115); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==T__0 );
				}
				break;
			case T__11:
				enterOuterAlt(_localctx, 6);
				{
				setState(117);
				match(T__11);
				setState(118);
				match(Integer);
				}
				break;
			case T__12:
				enterOuterAlt(_localctx, 7);
				{
				setState(119);
				match(T__12);
				setState(120);
				match(T__13);
				setState(121);
				match(T__0);
				setState(122);
				match(T__5);
				setState(123);
				match(T__0);
				setState(124);
				sort();
				setState(125);
				match(T__2);
				setState(126);
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

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3\26\u0085\4\2\t\2"+
		"\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13"+
		"\t\13\4\f\t\f\4\r\t\r\3\2\3\2\3\2\7\2\36\n\2\f\2\16\2!\13\2\3\2\7\2$\n"+
		"\2\f\2\16\2\'\13\2\3\2\3\2\3\3\3\3\3\3\3\3\3\3\3\3\3\4\3\4\3\4\3\4\3\4"+
		"\7\4\66\n\4\f\4\16\49\13\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\5\3\5"+
		"\3\5\3\5\3\5\3\6\3\6\3\6\5\6L\n\6\3\7\3\7\3\7\3\7\3\7\3\b\3\b\6\bU\n\b"+
		"\r\b\16\bV\3\t\3\t\3\n\3\n\3\13\3\13\3\f\3\f\3\r\3\r\3\r\3\r\3\r\6\rf"+
		"\n\r\r\r\16\rg\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\6\rt\n\r\r\r\16"+
		"\ru\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\5\r\u0083\n\r\3\r\2\2"+
		"\16\2\4\6\b\n\f\16\20\22\24\26\30\2\2\2\u0086\2\32\3\2\2\2\4*\3\2\2\2"+
		"\6\60\3\2\2\2\bC\3\2\2\2\nK\3\2\2\2\fM\3\2\2\2\16R\3\2\2\2\20X\3\2\2\2"+
		"\22Z\3\2\2\2\24\\\3\2\2\2\26^\3\2\2\2\30\u0082\3\2\2\2\32\33\7\3\2\2\33"+
		"\37\7\4\2\2\34\36\5\4\3\2\35\34\3\2\2\2\36!\3\2\2\2\37\35\3\2\2\2\37 "+
		"\3\2\2\2 %\3\2\2\2!\37\3\2\2\2\"$\5\6\4\2#\"\3\2\2\2$\'\3\2\2\2%#\3\2"+
		"\2\2%&\3\2\2\2&(\3\2\2\2\'%\3\2\2\2()\7\5\2\2)\3\3\2\2\2*+\7\3\2\2+,\7"+
		"\6\2\2,-\5\20\t\2-.\5\22\n\2./\7\5\2\2/\5\3\2\2\2\60\61\7\3\2\2\61\62"+
		"\7\7\2\2\62\63\5\24\13\2\63\67\7\3\2\2\64\66\5\b\5\2\65\64\3\2\2\2\66"+
		"9\3\2\2\2\67\65\3\2\2\2\678\3\2\2\28:\3\2\2\29\67\3\2\2\2:;\7\5\2\2;<"+
		"\7\3\2\2<=\5\n\6\2=>\7\5\2\2>?\7\3\2\2?@\5\30\r\2@A\7\5\2\2AB\7\5\2\2"+
		"B\7\3\2\2\2CD\7\3\2\2DE\5\26\f\2EF\5\n\6\2FG\7\5\2\2G\t\3\2\2\2HL\5\20"+
		"\t\2IL\5\16\b\2JL\5\f\7\2KH\3\2\2\2KI\3\2\2\2KJ\3\2\2\2L\13\3\2\2\2MN"+
		"\7\b\2\2NO\7\3\2\2OP\5\n\6\2PQ\7\5\2\2Q\r\3\2\2\2RT\7\t\2\2SU\5\n\6\2"+
		"TS\3\2\2\2UV\3\2\2\2VT\3\2\2\2VW\3\2\2\2W\17\3\2\2\2XY\7\21\2\2Y\21\3"+
		"\2\2\2Z[\7\23\2\2[\23\3\2\2\2\\]\7\21\2\2]\25\3\2\2\2^_\7\21\2\2_\27\3"+
		"\2\2\2`\u0083\7\23\2\2ab\7\n\2\2b\u0083\7\23\2\2ce\7\13\2\2df\5\30\r\2"+
		"ed\3\2\2\2fg\3\2\2\2ge\3\2\2\2gh\3\2\2\2h\u0083\3\2\2\2ij\7\f\2\2jk\7"+
		"\3\2\2kl\5\30\r\2lm\7\5\2\2m\u0083\3\2\2\2ns\7\r\2\2op\7\3\2\2pq\5\30"+
		"\r\2qr\7\5\2\2rt\3\2\2\2so\3\2\2\2tu\3\2\2\2us\3\2\2\2uv\3\2\2\2v\u0083"+
		"\3\2\2\2wx\7\16\2\2x\u0083\7\23\2\2yz\7\17\2\2z{\7\20\2\2{|\7\3\2\2|}"+
		"\7\b\2\2}~\7\3\2\2~\177\5\n\6\2\177\u0080\7\5\2\2\u0080\u0081\7\5\2\2"+
		"\u0081\u0083\3\2\2\2\u0082`\3\2\2\2\u0082a\3\2\2\2\u0082c\3\2\2\2\u0082"+
		"i\3\2\2\2\u0082n\3\2\2\2\u0082w\3\2\2\2\u0082y\3\2\2\2\u0083\31\3\2\2"+
		"\2\n\37%\67KVgu\u0082";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}