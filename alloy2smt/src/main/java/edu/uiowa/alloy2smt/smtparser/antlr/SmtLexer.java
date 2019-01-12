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
		T__9=10, UnaryOperator=11, BinaryOperator=12, TernaryOperator=13, MultiArityOperator=14, 
		AtomPrefix=15, Identifier=16, IdentifierLetter=17, Integer=18, Digit=19, 
		Comment=20, Whitespace=21;
	public static String[] channelNames = {
		"DEFAULT_TOKEN_CHANNEL", "HIDDEN"
	};

	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	private static String[] makeRuleNames() {
		return new String[] {
			"T__0", "T__1", "T__2", "T__3", "T__4", "T__5", "T__6", "T__7", "T__8", 
			"T__9", "UnaryOperator", "BinaryOperator", "TernaryOperator", "MultiArityOperator", 
			"AtomPrefix", "Identifier", "IdentifierLetter", "Integer", "Digit", "Comment", 
			"Whitespace"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'('", "'model'", "')'", "'declare-sort'", "'define-fun'", "'Set'", 
			"'Tuple'", "'-'", "'as'", "'emptyset'", null, null, "'ite'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, null, null, null, null, null, null, null, null, null, null, "UnaryOperator", 
			"BinaryOperator", "TernaryOperator", "MultiArityOperator", "AtomPrefix", 
			"Identifier", "IdentifierLetter", "Integer", "Digit", "Comment", "Whitespace"
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
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2\27\u012a\b\1\4\2"+
		"\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4"+
		"\13\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22"+
		"\t\22\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\3\2\3\2\3\3\3\3\3\3\3\3"+
		"\3\3\3\3\3\4\3\4\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3"+
		"\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\7\3\7\3\7\3\7\3\b\3\b\3\b"+
		"\3\b\3\b\3\b\3\t\3\t\3\n\3\n\3\n\3\13\3\13\3\13\3\13\3\13\3\13\3\13\3"+
		"\13\3\13\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3"+
		"\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f"+
		"\3\f\3\f\3\f\3\f\3\f\3\f\5\f\u008f\n\f\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r"+
		"\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3"+
		"\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r"+
		"\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3"+
		"\r\3\r\3\r\3\r\3\r\5\r\u00d2\n\r\3\16\3\16\3\16\3\16\3\17\3\17\3\17\3"+
		"\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3"+
		"\17\3\17\3\17\3\17\5\17\u00ed\n\17\3\20\3\20\3\20\3\20\3\20\3\20\3\20"+
		"\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20"+
		"\3\20\3\20\3\20\3\20\5\20\u0108\n\20\3\21\3\21\3\21\7\21\u010d\n\21\f"+
		"\21\16\21\u0110\13\21\3\22\3\22\3\23\6\23\u0115\n\23\r\23\16\23\u0116"+
		"\3\24\3\24\3\25\3\25\7\25\u011d\n\25\f\25\16\25\u0120\13\25\3\25\3\25"+
		"\3\26\6\26\u0125\n\26\r\26\16\26\u0126\3\26\3\26\2\2\27\3\3\5\4\7\5\t"+
		"\6\13\7\r\b\17\t\21\n\23\13\25\f\27\r\31\16\33\17\35\20\37\21!\22#\23"+
		"%\24\'\25)\26+\27\3\2\6\5\2,-//\61\61\5\2C\\aac|\4\2\f\f\17\17\5\2\13"+
		"\f\17\17\"\"\2\u0144\2\3\3\2\2\2\2\5\3\2\2\2\2\7\3\2\2\2\2\t\3\2\2\2\2"+
		"\13\3\2\2\2\2\r\3\2\2\2\2\17\3\2\2\2\2\21\3\2\2\2\2\23\3\2\2\2\2\25\3"+
		"\2\2\2\2\27\3\2\2\2\2\31\3\2\2\2\2\33\3\2\2\2\2\35\3\2\2\2\2\37\3\2\2"+
		"\2\2!\3\2\2\2\2#\3\2\2\2\2%\3\2\2\2\2\'\3\2\2\2\2)\3\2\2\2\2+\3\2\2\2"+
		"\3-\3\2\2\2\5/\3\2\2\2\7\65\3\2\2\2\t\67\3\2\2\2\13D\3\2\2\2\rO\3\2\2"+
		"\2\17S\3\2\2\2\21Y\3\2\2\2\23[\3\2\2\2\25^\3\2\2\2\27\u008e\3\2\2\2\31"+
		"\u00d1\3\2\2\2\33\u00d3\3\2\2\2\35\u00ec\3\2\2\2\37\u0107\3\2\2\2!\u0109"+
		"\3\2\2\2#\u0111\3\2\2\2%\u0114\3\2\2\2\'\u0118\3\2\2\2)\u011a\3\2\2\2"+
		"+\u0124\3\2\2\2-.\7*\2\2.\4\3\2\2\2/\60\7o\2\2\60\61\7q\2\2\61\62\7f\2"+
		"\2\62\63\7g\2\2\63\64\7n\2\2\64\6\3\2\2\2\65\66\7+\2\2\66\b\3\2\2\2\67"+
		"8\7f\2\289\7g\2\29:\7e\2\2:;\7n\2\2;<\7c\2\2<=\7t\2\2=>\7g\2\2>?\7/\2"+
		"\2?@\7u\2\2@A\7q\2\2AB\7t\2\2BC\7v\2\2C\n\3\2\2\2DE\7f\2\2EF\7g\2\2FG"+
		"\7h\2\2GH\7k\2\2HI\7p\2\2IJ\7g\2\2JK\7/\2\2KL\7h\2\2LM\7w\2\2MN\7p\2\2"+
		"N\f\3\2\2\2OP\7U\2\2PQ\7g\2\2QR\7v\2\2R\16\3\2\2\2ST\7V\2\2TU\7w\2\2U"+
		"V\7r\2\2VW\7n\2\2WX\7g\2\2X\20\3\2\2\2YZ\7/\2\2Z\22\3\2\2\2[\\\7c\2\2"+
		"\\]\7u\2\2]\24\3\2\2\2^_\7g\2\2_`\7o\2\2`a\7r\2\2ab\7v\2\2bc\7{\2\2cd"+
		"\7u\2\2de\7g\2\2ef\7v\2\2f\26\3\2\2\2gh\7p\2\2hi\7q\2\2i\u008f\7v\2\2"+
		"jk\7u\2\2kl\7k\2\2lm\7p\2\2mn\7i\2\2no\7n\2\2op\7g\2\2pq\7v\2\2qr\7q\2"+
		"\2r\u008f\7p\2\2st\7e\2\2tu\7q\2\2uv\7o\2\2vw\7r\2\2wx\7n\2\2xy\7g\2\2"+
		"yz\7o\2\2z{\7g\2\2{|\7p\2\2|\u008f\7v\2\2}~\7v\2\2~\177\7t\2\2\177\u0080"+
		"\7c\2\2\u0080\u0081\7p\2\2\u0081\u0082\7u\2\2\u0082\u0083\7r\2\2\u0083"+
		"\u0084\7q\2\2\u0084\u0085\7u\2\2\u0085\u008f\7g\2\2\u0086\u0087\7v\2\2"+
		"\u0087\u0088\7e\2\2\u0088\u0089\7n\2\2\u0089\u008a\7q\2\2\u008a\u008b"+
		"\7u\2\2\u008b\u008c\7w\2\2\u008c\u008d\7t\2\2\u008d\u008f\7g\2\2\u008e"+
		"g\3\2\2\2\u008ej\3\2\2\2\u008es\3\2\2\2\u008e}\3\2\2\2\u008e\u0086\3\2"+
		"\2\2\u008f\30\3\2\2\2\u0090\u00d2\4?@\2\u0091\u0092\7@\2\2\u0092\u00d2"+
		"\7?\2\2\u0093\u00d2\7>\2\2\u0094\u0095\7>\2\2\u0095\u00d2\7?\2\2\u0096"+
		"\u00d2\t\2\2\2\u0097\u0098\7o\2\2\u0098\u0099\7q\2\2\u0099\u00d2\7f\2"+
		"\2\u009a\u009b\7q\2\2\u009b\u00d2\7t\2\2\u009c\u009d\7c\2\2\u009d\u009e"+
		"\7p\2\2\u009e\u00d2\7f\2\2\u009f\u00a0\7?\2\2\u00a0\u00d2\7@\2\2\u00a1"+
		"\u00a2\7w\2\2\u00a2\u00a3\7p\2\2\u00a3\u00a4\7k\2\2\u00a4\u00a5\7q\2\2"+
		"\u00a5\u00d2\7p\2\2\u00a6\u00a7\7k\2\2\u00a7\u00a8\7p\2\2\u00a8\u00a9"+
		"\7v\2\2\u00a9\u00aa\7g\2\2\u00aa\u00ab\7t\2\2\u00ab\u00ac\7u\2\2\u00ac"+
		"\u00ad\7g\2\2\u00ad\u00ae\7e\2\2\u00ae\u00af\7v\2\2\u00af\u00b0\7k\2\2"+
		"\u00b0\u00b1\7q\2\2\u00b1\u00d2\7p\2\2\u00b2\u00b3\7u\2\2\u00b3\u00b4"+
		"\7g\2\2\u00b4\u00b5\7v\2\2\u00b5\u00b6\7o\2\2\u00b6\u00b7\7k\2\2\u00b7"+
		"\u00b8\7p\2\2\u00b8\u00b9\7w\2\2\u00b9\u00d2\7u\2\2\u00ba\u00bb\7o\2\2"+
		"\u00bb\u00bc\7g\2\2\u00bc\u00bd\7o\2\2\u00bd\u00be\7d\2\2\u00be\u00bf"+
		"\7g\2\2\u00bf\u00d2\7t\2\2\u00c0\u00c1\7u\2\2\u00c1\u00c2\7w\2\2\u00c2"+
		"\u00c3\7d\2\2\u00c3\u00c4\7u\2\2\u00c4\u00c5\7g\2\2\u00c5\u00d2\7v\2\2"+
		"\u00c6\u00c7\7l\2\2\u00c7\u00c8\7q\2\2\u00c8\u00c9\7k\2\2\u00c9\u00d2"+
		"\7p\2\2\u00ca\u00cb\7r\2\2\u00cb\u00cc\7t\2\2\u00cc\u00cd\7q\2\2\u00cd"+
		"\u00ce\7f\2\2\u00ce\u00cf\7w\2\2\u00cf\u00d0\7e\2\2\u00d0\u00d2\7v\2\2"+
		"\u00d1\u0090\3\2\2\2\u00d1\u0091\3\2\2\2\u00d1\u0093\3\2\2\2\u00d1\u0094"+
		"\3\2\2\2\u00d1\u0096\3\2\2\2\u00d1\u0097\3\2\2\2\u00d1\u009a\3\2\2\2\u00d1"+
		"\u009c\3\2\2\2\u00d1\u009f\3\2\2\2\u00d1\u00a1\3\2\2\2\u00d1\u00a6\3\2"+
		"\2\2\u00d1\u00b2\3\2\2\2\u00d1\u00ba\3\2\2\2\u00d1\u00c0\3\2\2\2\u00d1"+
		"\u00c6\3\2\2\2\u00d1\u00ca\3\2\2\2\u00d2\32\3\2\2\2\u00d3\u00d4\7k\2\2"+
		"\u00d4\u00d5\7v\2\2\u00d5\u00d6\7g\2\2\u00d6\34\3\2\2\2\u00d7\u00d8\7"+
		"o\2\2\u00d8\u00d9\7m\2\2\u00d9\u00da\7V\2\2\u00da\u00db\7w\2\2\u00db\u00dc"+
		"\7r\2\2\u00dc\u00dd\7n\2\2\u00dd\u00ed\7g\2\2\u00de\u00df\7k\2\2\u00df"+
		"\u00e0\7p\2\2\u00e0\u00e1\7u\2\2\u00e1\u00e2\7g\2\2\u00e2\u00e3\7t\2\2"+
		"\u00e3\u00ed\7v\2\2\u00e4\u00e5\7f\2\2\u00e5\u00e6\7k\2\2\u00e6\u00e7"+
		"\7u\2\2\u00e7\u00e8\7v\2\2\u00e8\u00e9\7k\2\2\u00e9\u00ea\7p\2\2\u00ea"+
		"\u00eb\7e\2\2\u00eb\u00ed\7v\2\2\u00ec\u00d7\3\2\2\2\u00ec\u00de\3\2\2"+
		"\2\u00ec\u00e4\3\2\2\2\u00ed\36\3\2\2\2\u00ee\u00ef\7B\2\2\u00ef\u00f0"+
		"\7w\2\2\u00f0\u00f1\7e\2\2\u00f1\u00f2\7a\2\2\u00f2\u00f3\7C\2\2\u00f3"+
		"\u00f4\7v\2\2\u00f4\u00f5\7q\2\2\u00f5\u00f6\7o\2\2\u00f6\u0108\7a\2\2"+
		"\u00f7\u00f8\7B\2\2\u00f8\u00f9\7w\2\2\u00f9\u00fa\7e\2\2\u00fa\u00fb"+
		"\7a\2\2\u00fb\u00fc\7W\2\2\u00fc\u00fd\7p\2\2\u00fd\u00fe\7c\2\2\u00fe"+
		"\u00ff\7t\2\2\u00ff\u0100\7{\2\2\u0100\u0101\7K\2\2\u0101\u0102\7p\2\2"+
		"\u0102\u0103\7v\2\2\u0103\u0104\7V\2\2\u0104\u0105\7w\2\2\u0105\u0106"+
		"\7r\2\2\u0106\u0108\7a\2\2\u0107\u00ee\3\2\2\2\u0107\u00f7\3\2\2\2\u0108"+
		" \3\2\2\2\u0109\u010e\5#\22\2\u010a\u010d\5#\22\2\u010b\u010d\5\'\24\2"+
		"\u010c\u010a\3\2\2\2\u010c\u010b\3\2\2\2\u010d\u0110\3\2\2\2\u010e\u010c"+
		"\3\2\2\2\u010e\u010f\3\2\2\2\u010f\"\3\2\2\2\u0110\u010e\3\2\2\2\u0111"+
		"\u0112\t\3\2\2\u0112$\3\2\2\2\u0113\u0115\5\'\24\2\u0114\u0113\3\2\2\2"+
		"\u0115\u0116\3\2\2\2\u0116\u0114\3\2\2\2\u0116\u0117\3\2\2\2\u0117&\3"+
		"\2\2\2\u0118\u0119\4\62;\2\u0119(\3\2\2\2\u011a\u011e\7=\2\2\u011b\u011d"+
		"\n\4\2\2\u011c\u011b\3\2\2\2\u011d\u0120\3\2\2\2\u011e\u011c\3\2\2\2\u011e"+
		"\u011f\3\2\2\2\u011f\u0121\3\2\2\2\u0120\u011e\3\2\2\2\u0121\u0122\b\25"+
		"\2\2\u0122*\3\2\2\2\u0123\u0125\t\5\2\2\u0124\u0123\3\2\2\2\u0125\u0126"+
		"\3\2\2\2\u0126\u0124\3\2\2\2\u0126\u0127\3\2\2\2\u0127\u0128\3\2\2\2\u0128"+
		"\u0129\b\26\2\2\u0129,\3\2\2\2\f\2\u008e\u00d1\u00ec\u0107\u010c\u010e"+
		"\u0116\u011e\u0126\3\b\2\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}