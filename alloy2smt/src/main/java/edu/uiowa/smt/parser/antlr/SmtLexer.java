// Generated from Smt.g4 by ANTLR 4.7.2
package edu.uiowa.smt.parser.antlr;
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class SmtLexer extends Lexer {
	static { RuntimeMetaData.checkVersion("4.7.2", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		T__0=1, T__1=2, T__2=3, T__3=4, T__4=5, T__5=6, T__6=7, T__7=8, T__8=9, 
		T__9=10, UnaryOperator=11, BinaryOperator=12, TernaryOperator=13, MultiArityOperator=14, 
		AtomPrefix=15, UninterpretedIntPrefix=16, Identifier=17, IdentifierLetter=18, 
		Integer=19, Digit=20, Comment=21, Whitespace=22;
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
			"AtomPrefix", "UninterpretedIntPrefix", "Identifier", "IdentifierLetter", 
			"Integer", "Digit", "Comment", "Whitespace"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'('", "'model'", "')'", "'declare-sort'", "'define-fun'", "'Set'", 
			"'Tuple'", "'-'", "'as'", "'emptyset'", null, null, "'ite'", null, "'@uc_Atom_'", 
			"'@uc_UninterpretedInt_'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, null, null, null, null, null, null, null, null, null, null, "UnaryOperator", 
			"BinaryOperator", "TernaryOperator", "MultiArityOperator", "AtomPrefix", 
			"UninterpretedIntPrefix", "Identifier", "IdentifierLetter", "Integer", 
			"Digit", "Comment", "Whitespace"
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
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2\30\u0131\b\1\4\2"+
		"\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4"+
		"\13\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22"+
		"\t\22\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\3\2\3\2\3\3\3"+
		"\3\3\3\3\3\3\3\3\3\3\4\3\4\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5"+
		"\3\5\3\5\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\7\3\7\3\7\3\7\3"+
		"\b\3\b\3\b\3\b\3\b\3\b\3\t\3\t\3\n\3\n\3\n\3\13\3\13\3\13\3\13\3\13\3"+
		"\13\3\13\3\13\3\13\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f"+
		"\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3"+
		"\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\5\f\u0091\n\f\3\r\3\r\3\r\3\r\3\r\3"+
		"\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r"+
		"\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3"+
		"\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r"+
		"\3\r\3\r\3\r\3\r\3\r\3\r\3\r\5\r\u00d4\n\r\3\16\3\16\3\16\3\16\3\17\3"+
		"\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3"+
		"\17\3\17\3\17\3\17\3\17\3\17\5\17\u00ef\n\17\3\20\3\20\3\20\3\20\3\20"+
		"\3\20\3\20\3\20\3\20\3\20\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21"+
		"\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\22"+
		"\3\22\3\22\7\22\u0114\n\22\f\22\16\22\u0117\13\22\3\23\3\23\3\24\6\24"+
		"\u011c\n\24\r\24\16\24\u011d\3\25\3\25\3\26\3\26\7\26\u0124\n\26\f\26"+
		"\16\26\u0127\13\26\3\26\3\26\3\27\6\27\u012c\n\27\r\27\16\27\u012d\3\27"+
		"\3\27\2\2\30\3\3\5\4\7\5\t\6\13\7\r\b\17\t\21\n\23\13\25\f\27\r\31\16"+
		"\33\17\35\20\37\21!\22#\23%\24\'\25)\26+\27-\30\3\2\6\5\2,-//\61\61\5"+
		"\2C\\aac|\4\2\f\f\17\17\5\2\13\f\17\17\"\"\2\u014a\2\3\3\2\2\2\2\5\3\2"+
		"\2\2\2\7\3\2\2\2\2\t\3\2\2\2\2\13\3\2\2\2\2\r\3\2\2\2\2\17\3\2\2\2\2\21"+
		"\3\2\2\2\2\23\3\2\2\2\2\25\3\2\2\2\2\27\3\2\2\2\2\31\3\2\2\2\2\33\3\2"+
		"\2\2\2\35\3\2\2\2\2\37\3\2\2\2\2!\3\2\2\2\2#\3\2\2\2\2%\3\2\2\2\2\'\3"+
		"\2\2\2\2)\3\2\2\2\2+\3\2\2\2\2-\3\2\2\2\3/\3\2\2\2\5\61\3\2\2\2\7\67\3"+
		"\2\2\2\t9\3\2\2\2\13F\3\2\2\2\rQ\3\2\2\2\17U\3\2\2\2\21[\3\2\2\2\23]\3"+
		"\2\2\2\25`\3\2\2\2\27\u0090\3\2\2\2\31\u00d3\3\2\2\2\33\u00d5\3\2\2\2"+
		"\35\u00ee\3\2\2\2\37\u00f0\3\2\2\2!\u00fa\3\2\2\2#\u0110\3\2\2\2%\u0118"+
		"\3\2\2\2\'\u011b\3\2\2\2)\u011f\3\2\2\2+\u0121\3\2\2\2-\u012b\3\2\2\2"+
		"/\60\7*\2\2\60\4\3\2\2\2\61\62\7o\2\2\62\63\7q\2\2\63\64\7f\2\2\64\65"+
		"\7g\2\2\65\66\7n\2\2\66\6\3\2\2\2\678\7+\2\28\b\3\2\2\29:\7f\2\2:;\7g"+
		"\2\2;<\7e\2\2<=\7n\2\2=>\7c\2\2>?\7t\2\2?@\7g\2\2@A\7/\2\2AB\7u\2\2BC"+
		"\7q\2\2CD\7t\2\2DE\7v\2\2E\n\3\2\2\2FG\7f\2\2GH\7g\2\2HI\7h\2\2IJ\7k\2"+
		"\2JK\7p\2\2KL\7g\2\2LM\7/\2\2MN\7h\2\2NO\7w\2\2OP\7p\2\2P\f\3\2\2\2QR"+
		"\7U\2\2RS\7g\2\2ST\7v\2\2T\16\3\2\2\2UV\7V\2\2VW\7w\2\2WX\7r\2\2XY\7n"+
		"\2\2YZ\7g\2\2Z\20\3\2\2\2[\\\7/\2\2\\\22\3\2\2\2]^\7c\2\2^_\7u\2\2_\24"+
		"\3\2\2\2`a\7g\2\2ab\7o\2\2bc\7r\2\2cd\7v\2\2de\7{\2\2ef\7u\2\2fg\7g\2"+
		"\2gh\7v\2\2h\26\3\2\2\2ij\7p\2\2jk\7q\2\2k\u0091\7v\2\2lm\7u\2\2mn\7k"+
		"\2\2no\7p\2\2op\7i\2\2pq\7n\2\2qr\7g\2\2rs\7v\2\2st\7q\2\2t\u0091\7p\2"+
		"\2uv\7e\2\2vw\7q\2\2wx\7o\2\2xy\7r\2\2yz\7n\2\2z{\7g\2\2{|\7o\2\2|}\7"+
		"g\2\2}~\7p\2\2~\u0091\7v\2\2\177\u0080\7v\2\2\u0080\u0081\7t\2\2\u0081"+
		"\u0082\7c\2\2\u0082\u0083\7p\2\2\u0083\u0084\7u\2\2\u0084\u0085\7r\2\2"+
		"\u0085\u0086\7q\2\2\u0086\u0087\7u\2\2\u0087\u0091\7g\2\2\u0088\u0089"+
		"\7v\2\2\u0089\u008a\7e\2\2\u008a\u008b\7n\2\2\u008b\u008c\7q\2\2\u008c"+
		"\u008d\7u\2\2\u008d\u008e\7w\2\2\u008e\u008f\7t\2\2\u008f\u0091\7g\2\2"+
		"\u0090i\3\2\2\2\u0090l\3\2\2\2\u0090u\3\2\2\2\u0090\177\3\2\2\2\u0090"+
		"\u0088\3\2\2\2\u0091\30\3\2\2\2\u0092\u00d4\4?@\2\u0093\u0094\7@\2\2\u0094"+
		"\u00d4\7?\2\2\u0095\u00d4\7>\2\2\u0096\u0097\7>\2\2\u0097\u00d4\7?\2\2"+
		"\u0098\u00d4\t\2\2\2\u0099\u009a\7o\2\2\u009a\u009b\7q\2\2\u009b\u00d4"+
		"\7f\2\2\u009c\u009d\7q\2\2\u009d\u00d4\7t\2\2\u009e\u009f\7c\2\2\u009f"+
		"\u00a0\7p\2\2\u00a0\u00d4\7f\2\2\u00a1\u00a2\7?\2\2\u00a2\u00d4\7@\2\2"+
		"\u00a3\u00a4\7w\2\2\u00a4\u00a5\7p\2\2\u00a5\u00a6\7k\2\2\u00a6\u00a7"+
		"\7q\2\2\u00a7\u00d4\7p\2\2\u00a8\u00a9\7k\2\2\u00a9\u00aa\7p\2\2\u00aa"+
		"\u00ab\7v\2\2\u00ab\u00ac\7g\2\2\u00ac\u00ad\7t\2\2\u00ad\u00ae\7u\2\2"+
		"\u00ae\u00af\7g\2\2\u00af\u00b0\7e\2\2\u00b0\u00b1\7v\2\2\u00b1\u00b2"+
		"\7k\2\2\u00b2\u00b3\7q\2\2\u00b3\u00d4\7p\2\2\u00b4\u00b5\7u\2\2\u00b5"+
		"\u00b6\7g\2\2\u00b6\u00b7\7v\2\2\u00b7\u00b8\7o\2\2\u00b8\u00b9\7k\2\2"+
		"\u00b9\u00ba\7p\2\2\u00ba\u00bb\7w\2\2\u00bb\u00d4\7u\2\2\u00bc\u00bd"+
		"\7o\2\2\u00bd\u00be\7g\2\2\u00be\u00bf\7o\2\2\u00bf\u00c0\7d\2\2\u00c0"+
		"\u00c1\7g\2\2\u00c1\u00d4\7t\2\2\u00c2\u00c3\7u\2\2\u00c3\u00c4\7w\2\2"+
		"\u00c4\u00c5\7d\2\2\u00c5\u00c6\7u\2\2\u00c6\u00c7\7g\2\2\u00c7\u00d4"+
		"\7v\2\2\u00c8\u00c9\7l\2\2\u00c9\u00ca\7q\2\2\u00ca\u00cb\7k\2\2\u00cb"+
		"\u00d4\7p\2\2\u00cc\u00cd\7r\2\2\u00cd\u00ce\7t\2\2\u00ce\u00cf\7q\2\2"+
		"\u00cf\u00d0\7f\2\2\u00d0\u00d1\7w\2\2\u00d1\u00d2\7e\2\2\u00d2\u00d4"+
		"\7v\2\2\u00d3\u0092\3\2\2\2\u00d3\u0093\3\2\2\2\u00d3\u0095\3\2\2\2\u00d3"+
		"\u0096\3\2\2\2\u00d3\u0098\3\2\2\2\u00d3\u0099\3\2\2\2\u00d3\u009c\3\2"+
		"\2\2\u00d3\u009e\3\2\2\2\u00d3\u00a1\3\2\2\2\u00d3\u00a3\3\2\2\2\u00d3"+
		"\u00a8\3\2\2\2\u00d3\u00b4\3\2\2\2\u00d3\u00bc\3\2\2\2\u00d3\u00c2\3\2"+
		"\2\2\u00d3\u00c8\3\2\2\2\u00d3\u00cc\3\2\2\2\u00d4\32\3\2\2\2\u00d5\u00d6"+
		"\7k\2\2\u00d6\u00d7\7v\2\2\u00d7\u00d8\7g\2\2\u00d8\34\3\2\2\2\u00d9\u00da"+
		"\7o\2\2\u00da\u00db\7m\2\2\u00db\u00dc\7V\2\2\u00dc\u00dd\7w\2\2\u00dd"+
		"\u00de\7r\2\2\u00de\u00df\7n\2\2\u00df\u00ef\7g\2\2\u00e0\u00e1\7k\2\2"+
		"\u00e1\u00e2\7p\2\2\u00e2\u00e3\7u\2\2\u00e3\u00e4\7g\2\2\u00e4\u00e5"+
		"\7t\2\2\u00e5\u00ef\7v\2\2\u00e6\u00e7\7f\2\2\u00e7\u00e8\7k\2\2\u00e8"+
		"\u00e9\7u\2\2\u00e9\u00ea\7v\2\2\u00ea\u00eb\7k\2\2\u00eb\u00ec\7p\2\2"+
		"\u00ec\u00ed\7e\2\2\u00ed\u00ef\7v\2\2\u00ee\u00d9\3\2\2\2\u00ee\u00e0"+
		"\3\2\2\2\u00ee\u00e6\3\2\2\2\u00ef\36\3\2\2\2\u00f0\u00f1\7B\2\2\u00f1"+
		"\u00f2\7w\2\2\u00f2\u00f3\7e\2\2\u00f3\u00f4\7a\2\2\u00f4\u00f5\7C\2\2"+
		"\u00f5\u00f6\7v\2\2\u00f6\u00f7\7q\2\2\u00f7\u00f8\7o\2\2\u00f8\u00f9"+
		"\7a\2\2\u00f9 \3\2\2\2\u00fa\u00fb\7B\2\2\u00fb\u00fc\7w\2\2\u00fc\u00fd"+
		"\7e\2\2\u00fd\u00fe\7a\2\2\u00fe\u00ff\7W\2\2\u00ff\u0100\7p\2\2\u0100"+
		"\u0101\7k\2\2\u0101\u0102\7p\2\2\u0102\u0103\7v\2\2\u0103\u0104\7g\2\2"+
		"\u0104\u0105\7t\2\2\u0105\u0106\7r\2\2\u0106\u0107\7t\2\2\u0107\u0108"+
		"\7g\2\2\u0108\u0109\7v\2\2\u0109\u010a\7g\2\2\u010a\u010b\7f\2\2\u010b"+
		"\u010c\7K\2\2\u010c\u010d\7p\2\2\u010d\u010e\7v\2\2\u010e\u010f\7a\2\2"+
		"\u010f\"\3\2\2\2\u0110\u0115\5%\23\2\u0111\u0114\5%\23\2\u0112\u0114\5"+
		")\25\2\u0113\u0111\3\2\2\2\u0113\u0112\3\2\2\2\u0114\u0117\3\2\2\2\u0115"+
		"\u0113\3\2\2\2\u0115\u0116\3\2\2\2\u0116$\3\2\2\2\u0117\u0115\3\2\2\2"+
		"\u0118\u0119\t\3\2\2\u0119&\3\2\2\2\u011a\u011c\5)\25\2\u011b\u011a\3"+
		"\2\2\2\u011c\u011d\3\2\2\2\u011d\u011b\3\2\2\2\u011d\u011e\3\2\2\2\u011e"+
		"(\3\2\2\2\u011f\u0120\4\62;\2\u0120*\3\2\2\2\u0121\u0125\7=\2\2\u0122"+
		"\u0124\n\4\2\2\u0123\u0122\3\2\2\2\u0124\u0127\3\2\2\2\u0125\u0123\3\2"+
		"\2\2\u0125\u0126\3\2\2\2\u0126\u0128\3\2\2\2\u0127\u0125\3\2\2\2\u0128"+
		"\u0129\b\26\2\2\u0129,\3\2\2\2\u012a\u012c\t\5\2\2\u012b\u012a\3\2\2\2"+
		"\u012c\u012d\3\2\2\2\u012d\u012b\3\2\2\2\u012d\u012e\3\2\2\2\u012e\u012f"+
		"\3\2\2\2\u012f\u0130\b\27\2\2\u0130.\3\2\2\2\13\2\u0090\u00d3\u00ee\u0113"+
		"\u0115\u011d\u0125\u012d\3\b\2\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}