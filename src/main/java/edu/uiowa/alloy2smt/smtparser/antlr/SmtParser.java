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
		RULE_model = 0, RULE_declarations = 1, RULE_definitions = 2, RULE_arguments = 3, 
		RULE_sort = 4, RULE_arity = 5, RULE_functionName = 6, RULE_argumentName = 7, 
		RULE_term = 8;
	private static String[] makeRuleNames() {
		return new String[] {
			"model", "declarations", "definitions", "arguments", "sort", "arity", 
			"functionName", "argumentName", "term"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'('", "'model'", "')'", "'declare-sort'", "'define-fun'", "'Tuple'", 
			"'Set'", "'-'", "'mkTuple'", "'singleton'", "'union'", "'@uc_Atom_'", 
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
		public List<DeclarationsContext> declarations() {
			return getRuleContexts(DeclarationsContext.class);
		}
		public DeclarationsContext declarations(int i) {
			return getRuleContext(DeclarationsContext.class,i);
		}
		public List<DefinitionsContext> definitions() {
			return getRuleContexts(DefinitionsContext.class);
		}
		public DefinitionsContext definitions(int i) {
			return getRuleContext(DefinitionsContext.class,i);
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
			setState(18);
			match(T__0);
			setState(19);
			match(T__1);
			setState(23);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,0,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					{
					{
					setState(20);
					declarations();
					}
					} 
				}
				setState(25);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,0,_ctx);
			}
			setState(29);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__0) {
				{
				{
				setState(26);
				definitions();
				}
				}
				setState(31);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(32);
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

	public static class DeclarationsContext extends ParserRuleContext {
		public SortContext sort() {
			return getRuleContext(SortContext.class,0);
		}
		public ArityContext arity() {
			return getRuleContext(ArityContext.class,0);
		}
		public DeclarationsContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_declarations; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterDeclarations(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitDeclarations(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitDeclarations(this);
			else return visitor.visitChildren(this);
		}
	}

	public final DeclarationsContext declarations() throws RecognitionException {
		DeclarationsContext _localctx = new DeclarationsContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_declarations);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(34);
			match(T__0);
			setState(35);
			match(T__3);
			setState(36);
			sort();
			setState(37);
			arity();
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

	public static class DefinitionsContext extends ParserRuleContext {
		public FunctionNameContext functionName() {
			return getRuleContext(FunctionNameContext.class,0);
		}
		public SortContext sort() {
			return getRuleContext(SortContext.class,0);
		}
		public TermContext term() {
			return getRuleContext(TermContext.class,0);
		}
		public List<ArgumentsContext> arguments() {
			return getRuleContexts(ArgumentsContext.class);
		}
		public ArgumentsContext arguments(int i) {
			return getRuleContext(ArgumentsContext.class,i);
		}
		public DefinitionsContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_definitions; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterDefinitions(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitDefinitions(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitDefinitions(this);
			else return visitor.visitChildren(this);
		}
	}

	public final DefinitionsContext definitions() throws RecognitionException {
		DefinitionsContext _localctx = new DefinitionsContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_definitions);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(40);
			match(T__0);
			setState(41);
			match(T__4);
			setState(42);
			functionName();
			setState(43);
			match(T__0);
			setState(47);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__0) {
				{
				{
				setState(44);
				arguments();
				}
				}
				setState(49);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(50);
			match(T__2);
			setState(51);
			match(T__0);
			setState(52);
			sort();
			setState(53);
			match(T__2);
			setState(54);
			match(T__0);
			setState(55);
			term();
			setState(56);
			match(T__2);
			setState(57);
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

	public static class ArgumentsContext extends ParserRuleContext {
		public ArgumentNameContext argumentName() {
			return getRuleContext(ArgumentNameContext.class,0);
		}
		public SortContext sort() {
			return getRuleContext(SortContext.class,0);
		}
		public ArgumentsContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_arguments; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).enterArguments(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SmtListener ) ((SmtListener)listener).exitArguments(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SmtVisitor ) return ((SmtVisitor<? extends T>)visitor).visitArguments(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ArgumentsContext arguments() throws RecognitionException {
		ArgumentsContext _localctx = new ArgumentsContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_arguments);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(59);
			match(T__0);
			setState(60);
			argumentName();
			setState(61);
			sort();
			setState(62);
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
		public TerminalNode Identifier() { return getToken(SmtParser.Identifier, 0); }
		public List<SortContext> sort() {
			return getRuleContexts(SortContext.class);
		}
		public SortContext sort(int i) {
			return getRuleContext(SortContext.class,i);
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
			int _alt;
			setState(76);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case Identifier:
				enterOuterAlt(_localctx, 1);
				{
				setState(64);
				match(Identifier);
				}
				break;
			case T__5:
				enterOuterAlt(_localctx, 2);
				{
				setState(65);
				match(T__5);
				setState(67); 
				_errHandler.sync(this);
				_alt = 1;
				do {
					switch (_alt) {
					case 1:
						{
						{
						setState(66);
						sort();
						}
						}
						break;
					default:
						throw new NoViableAltException(this);
					}
					setState(69); 
					_errHandler.sync(this);
					_alt = getInterpreter().adaptivePredict(_input,3,_ctx);
				} while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER );
				}
				break;
			case T__6:
				enterOuterAlt(_localctx, 3);
				{
				setState(71);
				match(T__6);
				setState(72);
				match(T__0);
				setState(73);
				sort();
				setState(74);
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
		enterRule(_localctx, 10, RULE_arity);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(78);
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
		enterRule(_localctx, 12, RULE_functionName);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(80);
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
		enterRule(_localctx, 14, RULE_argumentName);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(82);
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
		enterRule(_localctx, 16, RULE_term);
		int _la;
		try {
			int _alt;
			setState(118);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case Integer:
				enterOuterAlt(_localctx, 1);
				{
				setState(84);
				match(Integer);
				}
				break;
			case T__7:
				enterOuterAlt(_localctx, 2);
				{
				setState(85);
				match(T__7);
				setState(86);
				match(Integer);
				}
				break;
			case T__8:
				enterOuterAlt(_localctx, 3);
				{
				setState(87);
				match(T__8);
				setState(89); 
				_errHandler.sync(this);
				_alt = 1;
				do {
					switch (_alt) {
					case 1:
						{
						{
						setState(88);
						term();
						}
						}
						break;
					default:
						throw new NoViableAltException(this);
					}
					setState(91); 
					_errHandler.sync(this);
					_alt = getInterpreter().adaptivePredict(_input,5,_ctx);
				} while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER );
				}
				break;
			case T__9:
				enterOuterAlt(_localctx, 4);
				{
				setState(93);
				match(T__9);
				setState(94);
				match(T__0);
				setState(95);
				term();
				setState(96);
				match(T__2);
				}
				break;
			case T__10:
				enterOuterAlt(_localctx, 5);
				{
				setState(98);
				match(T__10);
				setState(103); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(99);
					match(T__0);
					setState(100);
					term();
					setState(101);
					match(T__2);
					}
					}
					setState(105); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==T__0 );
				}
				break;
			case T__11:
				enterOuterAlt(_localctx, 6);
				{
				setState(107);
				match(T__11);
				setState(108);
				match(Integer);
				}
				break;
			case T__12:
				enterOuterAlt(_localctx, 7);
				{
				setState(109);
				match(T__12);
				setState(110);
				match(T__13);
				setState(111);
				match(T__0);
				setState(112);
				match(T__6);
				setState(113);
				match(T__0);
				setState(114);
				sort();
				setState(115);
				match(T__2);
				setState(116);
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
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3\26{\4\2\t\2\4\3\t"+
		"\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\3\2\3\2\3\2"+
		"\7\2\30\n\2\f\2\16\2\33\13\2\3\2\7\2\36\n\2\f\2\16\2!\13\2\3\2\3\2\3\3"+
		"\3\3\3\3\3\3\3\3\3\3\3\4\3\4\3\4\3\4\3\4\7\4\60\n\4\f\4\16\4\63\13\4\3"+
		"\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\5\3\5\3\5\3\5\3\5\3\6\3\6\3\6\6\6"+
		"F\n\6\r\6\16\6G\3\6\3\6\3\6\3\6\3\6\5\6O\n\6\3\7\3\7\3\b\3\b\3\t\3\t\3"+
		"\n\3\n\3\n\3\n\3\n\6\n\\\n\n\r\n\16\n]\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n"+
		"\3\n\3\n\6\nj\n\n\r\n\16\nk\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3"+
		"\n\5\ny\n\n\3\n\2\2\13\2\4\6\b\n\f\16\20\22\2\2\2\177\2\24\3\2\2\2\4$"+
		"\3\2\2\2\6*\3\2\2\2\b=\3\2\2\2\nN\3\2\2\2\fP\3\2\2\2\16R\3\2\2\2\20T\3"+
		"\2\2\2\22x\3\2\2\2\24\25\7\3\2\2\25\31\7\4\2\2\26\30\5\4\3\2\27\26\3\2"+
		"\2\2\30\33\3\2\2\2\31\27\3\2\2\2\31\32\3\2\2\2\32\37\3\2\2\2\33\31\3\2"+
		"\2\2\34\36\5\6\4\2\35\34\3\2\2\2\36!\3\2\2\2\37\35\3\2\2\2\37 \3\2\2\2"+
		" \"\3\2\2\2!\37\3\2\2\2\"#\7\5\2\2#\3\3\2\2\2$%\7\3\2\2%&\7\6\2\2&\'\5"+
		"\n\6\2\'(\5\f\7\2()\7\5\2\2)\5\3\2\2\2*+\7\3\2\2+,\7\7\2\2,-\5\16\b\2"+
		"-\61\7\3\2\2.\60\5\b\5\2/.\3\2\2\2\60\63\3\2\2\2\61/\3\2\2\2\61\62\3\2"+
		"\2\2\62\64\3\2\2\2\63\61\3\2\2\2\64\65\7\5\2\2\65\66\7\3\2\2\66\67\5\n"+
		"\6\2\678\7\5\2\289\7\3\2\29:\5\22\n\2:;\7\5\2\2;<\7\5\2\2<\7\3\2\2\2="+
		">\7\3\2\2>?\5\20\t\2?@\5\n\6\2@A\7\5\2\2A\t\3\2\2\2BO\7\21\2\2CE\7\b\2"+
		"\2DF\5\n\6\2ED\3\2\2\2FG\3\2\2\2GE\3\2\2\2GH\3\2\2\2HO\3\2\2\2IJ\7\t\2"+
		"\2JK\7\3\2\2KL\5\n\6\2LM\7\5\2\2MO\3\2\2\2NB\3\2\2\2NC\3\2\2\2NI\3\2\2"+
		"\2O\13\3\2\2\2PQ\7\23\2\2Q\r\3\2\2\2RS\7\21\2\2S\17\3\2\2\2TU\7\21\2\2"+
		"U\21\3\2\2\2Vy\7\23\2\2WX\7\n\2\2Xy\7\23\2\2Y[\7\13\2\2Z\\\5\22\n\2[Z"+
		"\3\2\2\2\\]\3\2\2\2][\3\2\2\2]^\3\2\2\2^y\3\2\2\2_`\7\f\2\2`a\7\3\2\2"+
		"ab\5\22\n\2bc\7\5\2\2cy\3\2\2\2di\7\r\2\2ef\7\3\2\2fg\5\22\n\2gh\7\5\2"+
		"\2hj\3\2\2\2ie\3\2\2\2jk\3\2\2\2ki\3\2\2\2kl\3\2\2\2ly\3\2\2\2mn\7\16"+
		"\2\2ny\7\23\2\2op\7\17\2\2pq\7\20\2\2qr\7\3\2\2rs\7\t\2\2st\7\3\2\2tu"+
		"\5\n\6\2uv\7\5\2\2vw\7\5\2\2wy\3\2\2\2xV\3\2\2\2xW\3\2\2\2xY\3\2\2\2x"+
		"_\3\2\2\2xd\3\2\2\2xm\3\2\2\2xo\3\2\2\2y\23\3\2\2\2\n\31\37\61GN]kx";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}