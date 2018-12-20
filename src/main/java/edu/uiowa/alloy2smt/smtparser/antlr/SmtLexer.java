// Generated from Smt.g4 by ANTLR 4.7.2
package edu.uiowa.alloy2smt.smtparser.antlr;
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.misc.*;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class SmtLexer extends Lexer {
	static { RuntimeMetaData.checkVersion("4.7.2", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		T__0=1, T__1=2, T__2=3, T__3=4, T__4=5, T__5=6, T__6=7, T__7=8, T__8=9, 
		T__9=10, T__10=11, T__11=12, T__12=13, T__13=14, Identifier=15, IdentifierLetter=16, 
		Integer=17, Digit=18, Comment=19, Whitespace=20;
	public static String[] channelNames = {
		"DEFAULT_TOKEN_CHANNEL", "HIDDEN"
	};

	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	private static String[] makeRuleNames() {
		return new String[] {
			"T__0", "T__1", "T__2", "T__3", "T__4", "T__5", "T__6", "T__7", "T__8", 
			"T__9", "T__10", "T__11", "T__12", "T__13", "Identifier", "IdentifierLetter", 
			"Integer", "Digit", "Comment", "Whitespace"
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


	public SmtLexer(CharStream input) {
		super(input);
		_interp = new LexerATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@Override
	public String getGrammarFileName() { return "Smt.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public String[] getChannelNames() { return channelNames; }

	@Override
	public String[] getModeNames() { return modeNames; }

	@Override
	public ATN getATN() { return _ATN; }

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2\26\u00a8\b\1\4\2"+
		"\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4"+
		"\13\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22"+
		"\t\22\4\23\t\23\4\24\t\24\4\25\t\25\3\2\3\2\3\3\3\3\3\3\3\3\3\3\3\3\3"+
		"\4\3\4\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\6\3\6\3\6"+
		"\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\7\3\7\3\7\3\7\3\7\3\7\3\b\3\b\3\b\3"+
		"\b\3\t\3\t\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\13\3\13\3\13\3\13\3\13\3"+
		"\13\3\13\3\13\3\13\3\13\3\f\3\f\3\f\3\f\3\f\3\f\3\r\3\r\3\r\3\r\3\r\3"+
		"\r\3\r\3\r\3\r\3\r\3\16\3\16\3\16\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3"+
		"\17\3\17\3\20\3\20\3\20\7\20\u008b\n\20\f\20\16\20\u008e\13\20\3\21\3"+
		"\21\3\22\6\22\u0093\n\22\r\22\16\22\u0094\3\23\3\23\3\24\3\24\7\24\u009b"+
		"\n\24\f\24\16\24\u009e\13\24\3\24\3\24\3\25\6\25\u00a3\n\25\r\25\16\25"+
		"\u00a4\3\25\3\25\2\2\26\3\3\5\4\7\5\t\6\13\7\r\b\17\t\21\n\23\13\25\f"+
		"\27\r\31\16\33\17\35\20\37\21!\22#\23%\24\'\25)\26\3\2\5\5\2C\\aac|\4"+
		"\2\f\f\17\17\5\2\13\f\17\17\"\"\2\u00ac\2\3\3\2\2\2\2\5\3\2\2\2\2\7\3"+
		"\2\2\2\2\t\3\2\2\2\2\13\3\2\2\2\2\r\3\2\2\2\2\17\3\2\2\2\2\21\3\2\2\2"+
		"\2\23\3\2\2\2\2\25\3\2\2\2\2\27\3\2\2\2\2\31\3\2\2\2\2\33\3\2\2\2\2\35"+
		"\3\2\2\2\2\37\3\2\2\2\2!\3\2\2\2\2#\3\2\2\2\2%\3\2\2\2\2\'\3\2\2\2\2)"+
		"\3\2\2\2\3+\3\2\2\2\5-\3\2\2\2\7\63\3\2\2\2\t\65\3\2\2\2\13B\3\2\2\2\r"+
		"M\3\2\2\2\17S\3\2\2\2\21W\3\2\2\2\23Y\3\2\2\2\25a\3\2\2\2\27k\3\2\2\2"+
		"\31q\3\2\2\2\33{\3\2\2\2\35~\3\2\2\2\37\u0087\3\2\2\2!\u008f\3\2\2\2#"+
		"\u0092\3\2\2\2%\u0096\3\2\2\2\'\u0098\3\2\2\2)\u00a2\3\2\2\2+,\7*\2\2"+
		",\4\3\2\2\2-.\7o\2\2./\7q\2\2/\60\7f\2\2\60\61\7g\2\2\61\62\7n\2\2\62"+
		"\6\3\2\2\2\63\64\7+\2\2\64\b\3\2\2\2\65\66\7f\2\2\66\67\7g\2\2\678\7e"+
		"\2\289\7n\2\29:\7c\2\2:;\7t\2\2;<\7g\2\2<=\7/\2\2=>\7u\2\2>?\7q\2\2?@"+
		"\7t\2\2@A\7v\2\2A\n\3\2\2\2BC\7f\2\2CD\7g\2\2DE\7h\2\2EF\7k\2\2FG\7p\2"+
		"\2GH\7g\2\2HI\7/\2\2IJ\7h\2\2JK\7w\2\2KL\7p\2\2L\f\3\2\2\2MN\7V\2\2NO"+
		"\7w\2\2OP\7r\2\2PQ\7n\2\2QR\7g\2\2R\16\3\2\2\2ST\7U\2\2TU\7g\2\2UV\7v"+
		"\2\2V\20\3\2\2\2WX\7/\2\2X\22\3\2\2\2YZ\7o\2\2Z[\7m\2\2[\\\7V\2\2\\]\7"+
		"w\2\2]^\7r\2\2^_\7n\2\2_`\7g\2\2`\24\3\2\2\2ab\7u\2\2bc\7k\2\2cd\7p\2"+
		"\2de\7i\2\2ef\7n\2\2fg\7g\2\2gh\7v\2\2hi\7q\2\2ij\7p\2\2j\26\3\2\2\2k"+
		"l\7w\2\2lm\7p\2\2mn\7k\2\2no\7q\2\2op\7p\2\2p\30\3\2\2\2qr\7B\2\2rs\7"+
		"w\2\2st\7e\2\2tu\7a\2\2uv\7C\2\2vw\7v\2\2wx\7q\2\2xy\7o\2\2yz\7a\2\2z"+
		"\32\3\2\2\2{|\7c\2\2|}\7u\2\2}\34\3\2\2\2~\177\7g\2\2\177\u0080\7o\2\2"+
		"\u0080\u0081\7r\2\2\u0081\u0082\7v\2\2\u0082\u0083\7{\2\2\u0083\u0084"+
		"\7u\2\2\u0084\u0085\7g\2\2\u0085\u0086\7v\2\2\u0086\36\3\2\2\2\u0087\u008c"+
		"\5!\21\2\u0088\u008b\5!\21\2\u0089\u008b\5%\23\2\u008a\u0088\3\2\2\2\u008a"+
		"\u0089\3\2\2\2\u008b\u008e\3\2\2\2\u008c\u008a\3\2\2\2\u008c\u008d\3\2"+
		"\2\2\u008d \3\2\2\2\u008e\u008c\3\2\2\2\u008f\u0090\t\2\2\2\u0090\"\3"+
		"\2\2\2\u0091\u0093\5%\23\2\u0092\u0091\3\2\2\2\u0093\u0094\3\2\2\2\u0094"+
		"\u0092\3\2\2\2\u0094\u0095\3\2\2\2\u0095$\3\2\2\2\u0096\u0097\4\62;\2"+
		"\u0097&\3\2\2\2\u0098\u009c\7=\2\2\u0099\u009b\n\3\2\2\u009a\u0099\3\2"+
		"\2\2\u009b\u009e\3\2\2\2\u009c\u009a\3\2\2\2\u009c\u009d\3\2\2\2\u009d"+
		"\u009f\3\2\2\2\u009e\u009c\3\2\2\2\u009f\u00a0\b\24\2\2\u00a0(\3\2\2\2"+
		"\u00a1\u00a3\t\4\2\2\u00a2\u00a1\3\2\2\2\u00a3\u00a4\3\2\2\2\u00a4\u00a2"+
		"\3\2\2\2\u00a4\u00a5\3\2\2\2\u00a5\u00a6\3\2\2\2\u00a6\u00a7\b\25\2\2"+
		"\u00a7*\3\2\2\2\b\2\u008a\u008c\u0094\u009c\u00a4\3\b\2\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}