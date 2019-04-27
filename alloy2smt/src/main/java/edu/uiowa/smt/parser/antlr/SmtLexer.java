// Generated from Smt.g4 by ANTLR 4.7.2
package edu.uiowa.smt.parser.antlr;
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
		T__9=10, True=11, False=12, UnaryOperator=13, BinaryOperator=14, TernaryOperator=15, 
		MultiArityOperator=16, AtomPrefix=17, UninterpretedIntPrefix=18, Identifier=19, 
		IdentifierLetter=20, Integer=21, Digit=22, Comment=23, Whitespace=24;
	public static String[] channelNames = {
		"DEFAULT_TOKEN_CHANNEL", "HIDDEN"
	};

	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	private static String[] makeRuleNames() {
		return new String[] {
			"T__0", "T__1", "T__2", "T__3", "T__4", "T__5", "T__6", "T__7", "T__8", 
			"T__9", "True", "False", "UnaryOperator", "BinaryOperator", "TernaryOperator", 
			"MultiArityOperator", "AtomPrefix", "UninterpretedIntPrefix", "Identifier", 
			"IdentifierLetter", "Integer", "Digit", "Comment", "Whitespace"
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
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2\32\u0140\b\1\4\2"+
		"\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4"+
		"\13\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22"+
		"\t\22\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31"+
		"\t\31\3\2\3\2\3\3\3\3\3\3\3\3\3\3\3\3\3\4\3\4\3\5\3\5\3\5\3\5\3\5\3\5"+
		"\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3"+
		"\6\3\7\3\7\3\7\3\7\3\b\3\b\3\b\3\b\3\b\3\b\3\t\3\t\3\n\3\n\3\n\3\13\3"+
		"\13\3\13\3\13\3\13\3\13\3\13\3\13\3\13\3\f\3\f\3\f\3\f\3\f\3\r\3\r\3\r"+
		"\3\r\3\r\3\r\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3"+
		"\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3"+
		"\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\5"+
		"\16\u00a0\n\16\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17"+
		"\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17"+
		"\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17"+
		"\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17"+
		"\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\5\17\u00e3"+
		"\n\17\3\20\3\20\3\20\3\20\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21"+
		"\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\5\21\u00fe"+
		"\n\21\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\23\3\23\3\23"+
		"\3\23\3\23\3\23\3\23\3\23\3\23\3\23\3\23\3\23\3\23\3\23\3\23\3\23\3\23"+
		"\3\23\3\23\3\23\3\23\3\23\3\24\3\24\3\24\7\24\u0123\n\24\f\24\16\24\u0126"+
		"\13\24\3\25\3\25\3\26\6\26\u012b\n\26\r\26\16\26\u012c\3\27\3\27\3\30"+
		"\3\30\7\30\u0133\n\30\f\30\16\30\u0136\13\30\3\30\3\30\3\31\6\31\u013b"+
		"\n\31\r\31\16\31\u013c\3\31\3\31\2\2\32\3\3\5\4\7\5\t\6\13\7\r\b\17\t"+
		"\21\n\23\13\25\f\27\r\31\16\33\17\35\20\37\21!\22#\23%\24\'\25)\26+\27"+
		"-\30/\31\61\32\3\2\6\5\2,-//\61\61\5\2C\\aac|\4\2\f\f\17\17\5\2\13\f\17"+
		"\17\"\"\2\u0159\2\3\3\2\2\2\2\5\3\2\2\2\2\7\3\2\2\2\2\t\3\2\2\2\2\13\3"+
		"\2\2\2\2\r\3\2\2\2\2\17\3\2\2\2\2\21\3\2\2\2\2\23\3\2\2\2\2\25\3\2\2\2"+
		"\2\27\3\2\2\2\2\31\3\2\2\2\2\33\3\2\2\2\2\35\3\2\2\2\2\37\3\2\2\2\2!\3"+
		"\2\2\2\2#\3\2\2\2\2%\3\2\2\2\2\'\3\2\2\2\2)\3\2\2\2\2+\3\2\2\2\2-\3\2"+
		"\2\2\2/\3\2\2\2\2\61\3\2\2\2\3\63\3\2\2\2\5\65\3\2\2\2\7;\3\2\2\2\t=\3"+
		"\2\2\2\13J\3\2\2\2\rU\3\2\2\2\17Y\3\2\2\2\21_\3\2\2\2\23a\3\2\2\2\25d"+
		"\3\2\2\2\27m\3\2\2\2\31r\3\2\2\2\33\u009f\3\2\2\2\35\u00e2\3\2\2\2\37"+
		"\u00e4\3\2\2\2!\u00fd\3\2\2\2#\u00ff\3\2\2\2%\u0109\3\2\2\2\'\u011f\3"+
		"\2\2\2)\u0127\3\2\2\2+\u012a\3\2\2\2-\u012e\3\2\2\2/\u0130\3\2\2\2\61"+
		"\u013a\3\2\2\2\63\64\7*\2\2\64\4\3\2\2\2\65\66\7o\2\2\66\67\7q\2\2\67"+
		"8\7f\2\289\7g\2\29:\7n\2\2:\6\3\2\2\2;<\7+\2\2<\b\3\2\2\2=>\7f\2\2>?\7"+
		"g\2\2?@\7e\2\2@A\7n\2\2AB\7c\2\2BC\7t\2\2CD\7g\2\2DE\7/\2\2EF\7u\2\2F"+
		"G\7q\2\2GH\7t\2\2HI\7v\2\2I\n\3\2\2\2JK\7f\2\2KL\7g\2\2LM\7h\2\2MN\7k"+
		"\2\2NO\7p\2\2OP\7g\2\2PQ\7/\2\2QR\7h\2\2RS\7w\2\2ST\7p\2\2T\f\3\2\2\2"+
		"UV\7U\2\2VW\7g\2\2WX\7v\2\2X\16\3\2\2\2YZ\7V\2\2Z[\7w\2\2[\\\7r\2\2\\"+
		"]\7n\2\2]^\7g\2\2^\20\3\2\2\2_`\7/\2\2`\22\3\2\2\2ab\7c\2\2bc\7u\2\2c"+
		"\24\3\2\2\2de\7g\2\2ef\7o\2\2fg\7r\2\2gh\7v\2\2hi\7{\2\2ij\7u\2\2jk\7"+
		"g\2\2kl\7v\2\2l\26\3\2\2\2mn\7v\2\2no\7t\2\2op\7w\2\2pq\7g\2\2q\30\3\2"+
		"\2\2rs\7h\2\2st\7c\2\2tu\7n\2\2uv\7u\2\2vw\7g\2\2w\32\3\2\2\2xy\7p\2\2"+
		"yz\7q\2\2z\u00a0\7v\2\2{|\7u\2\2|}\7k\2\2}~\7p\2\2~\177\7i\2\2\177\u0080"+
		"\7n\2\2\u0080\u0081\7g\2\2\u0081\u0082\7v\2\2\u0082\u0083\7q\2\2\u0083"+
		"\u00a0\7p\2\2\u0084\u0085\7e\2\2\u0085\u0086\7q\2\2\u0086\u0087\7o\2\2"+
		"\u0087\u0088\7r\2\2\u0088\u0089\7n\2\2\u0089\u008a\7g\2\2\u008a\u008b"+
		"\7o\2\2\u008b\u008c\7g\2\2\u008c\u008d\7p\2\2\u008d\u00a0\7v\2\2\u008e"+
		"\u008f\7v\2\2\u008f\u0090\7t\2\2\u0090\u0091\7c\2\2\u0091\u0092\7p\2\2"+
		"\u0092\u0093\7u\2\2\u0093\u0094\7r\2\2\u0094\u0095\7q\2\2\u0095\u0096"+
		"\7u\2\2\u0096\u00a0\7g\2\2\u0097\u0098\7v\2\2\u0098\u0099\7e\2\2\u0099"+
		"\u009a\7n\2\2\u009a\u009b\7q\2\2\u009b\u009c\7u\2\2\u009c\u009d\7w\2\2"+
		"\u009d\u009e\7t\2\2\u009e\u00a0\7g\2\2\u009fx\3\2\2\2\u009f{\3\2\2\2\u009f"+
		"\u0084\3\2\2\2\u009f\u008e\3\2\2\2\u009f\u0097\3\2\2\2\u00a0\34\3\2\2"+
		"\2\u00a1\u00e3\4?@\2\u00a2\u00a3\7@\2\2\u00a3\u00e3\7?\2\2\u00a4\u00e3"+
		"\7>\2\2\u00a5\u00a6\7>\2\2\u00a6\u00e3\7?\2\2\u00a7\u00e3\t\2\2\2\u00a8"+
		"\u00a9\7o\2\2\u00a9\u00aa\7q\2\2\u00aa\u00e3\7f\2\2\u00ab\u00ac\7q\2\2"+
		"\u00ac\u00e3\7t\2\2\u00ad\u00ae\7c\2\2\u00ae\u00af\7p\2\2\u00af\u00e3"+
		"\7f\2\2\u00b0\u00b1\7?\2\2\u00b1\u00e3\7@\2\2\u00b2\u00b3\7w\2\2\u00b3"+
		"\u00b4\7p\2\2\u00b4\u00b5\7k\2\2\u00b5\u00b6\7q\2\2\u00b6\u00e3\7p\2\2"+
		"\u00b7\u00b8\7k\2\2\u00b8\u00b9\7p\2\2\u00b9\u00ba\7v\2\2\u00ba\u00bb"+
		"\7g\2\2\u00bb\u00bc\7t\2\2\u00bc\u00bd\7u\2\2\u00bd\u00be\7g\2\2\u00be"+
		"\u00bf\7e\2\2\u00bf\u00c0\7v\2\2\u00c0\u00c1\7k\2\2\u00c1\u00c2\7q\2\2"+
		"\u00c2\u00e3\7p\2\2\u00c3\u00c4\7u\2\2\u00c4\u00c5\7g\2\2\u00c5\u00c6"+
		"\7v\2\2\u00c6\u00c7\7o\2\2\u00c7\u00c8\7k\2\2\u00c8\u00c9\7p\2\2\u00c9"+
		"\u00ca\7w\2\2\u00ca\u00e3\7u\2\2\u00cb\u00cc\7o\2\2\u00cc\u00cd\7g\2\2"+
		"\u00cd\u00ce\7o\2\2\u00ce\u00cf\7d\2\2\u00cf\u00d0\7g\2\2\u00d0\u00e3"+
		"\7t\2\2\u00d1\u00d2\7u\2\2\u00d2\u00d3\7w\2\2\u00d3\u00d4\7d\2\2\u00d4"+
		"\u00d5\7u\2\2\u00d5\u00d6\7g\2\2\u00d6\u00e3\7v\2\2\u00d7\u00d8\7l\2\2"+
		"\u00d8\u00d9\7q\2\2\u00d9\u00da\7k\2\2\u00da\u00e3\7p\2\2\u00db\u00dc"+
		"\7r\2\2\u00dc\u00dd\7t\2\2\u00dd\u00de\7q\2\2\u00de\u00df\7f\2\2\u00df"+
		"\u00e0\7w\2\2\u00e0\u00e1\7e\2\2\u00e1\u00e3\7v\2\2\u00e2\u00a1\3\2\2"+
		"\2\u00e2\u00a2\3\2\2\2\u00e2\u00a4\3\2\2\2\u00e2\u00a5\3\2\2\2\u00e2\u00a7"+
		"\3\2\2\2\u00e2\u00a8\3\2\2\2\u00e2\u00ab\3\2\2\2\u00e2\u00ad\3\2\2\2\u00e2"+
		"\u00b0\3\2\2\2\u00e2\u00b2\3\2\2\2\u00e2\u00b7\3\2\2\2\u00e2\u00c3\3\2"+
		"\2\2\u00e2\u00cb\3\2\2\2\u00e2\u00d1\3\2\2\2\u00e2\u00d7\3\2\2\2\u00e2"+
		"\u00db\3\2\2\2\u00e3\36\3\2\2\2\u00e4\u00e5\7k\2\2\u00e5\u00e6\7v\2\2"+
		"\u00e6\u00e7\7g\2\2\u00e7 \3\2\2\2\u00e8\u00e9\7o\2\2\u00e9\u00ea\7m\2"+
		"\2\u00ea\u00eb\7V\2\2\u00eb\u00ec\7w\2\2\u00ec\u00ed\7r\2\2\u00ed\u00ee"+
		"\7n\2\2\u00ee\u00fe\7g\2\2\u00ef\u00f0\7k\2\2\u00f0\u00f1\7p\2\2\u00f1"+
		"\u00f2\7u\2\2\u00f2\u00f3\7g\2\2\u00f3\u00f4\7t\2\2\u00f4\u00fe\7v\2\2"+
		"\u00f5\u00f6\7f\2\2\u00f6\u00f7\7k\2\2\u00f7\u00f8\7u\2\2\u00f8\u00f9"+
		"\7v\2\2\u00f9\u00fa\7k\2\2\u00fa\u00fb\7p\2\2\u00fb\u00fc\7e\2\2\u00fc"+
		"\u00fe\7v\2\2\u00fd\u00e8\3\2\2\2\u00fd\u00ef\3\2\2\2\u00fd\u00f5\3\2"+
		"\2\2\u00fe\"\3\2\2\2\u00ff\u0100\7B\2\2\u0100\u0101\7w\2\2\u0101\u0102"+
		"\7e\2\2\u0102\u0103\7a\2\2\u0103\u0104\7C\2\2\u0104\u0105\7v\2\2\u0105"+
		"\u0106\7q\2\2\u0106\u0107\7o\2\2\u0107\u0108\7a\2\2\u0108$\3\2\2\2\u0109"+
		"\u010a\7B\2\2\u010a\u010b\7w\2\2\u010b\u010c\7e\2\2\u010c\u010d\7a\2\2"+
		"\u010d\u010e\7W\2\2\u010e\u010f\7p\2\2\u010f\u0110\7k\2\2\u0110\u0111"+
		"\7p\2\2\u0111\u0112\7v\2\2\u0112\u0113\7g\2\2\u0113\u0114\7t\2\2\u0114"+
		"\u0115\7r\2\2\u0115\u0116\7t\2\2\u0116\u0117\7g\2\2\u0117\u0118\7v\2\2"+
		"\u0118\u0119\7g\2\2\u0119\u011a\7f\2\2\u011a\u011b\7K\2\2\u011b\u011c"+
		"\7p\2\2\u011c\u011d\7v\2\2\u011d\u011e\7a\2\2\u011e&\3\2\2\2\u011f\u0124"+
		"\5)\25\2\u0120\u0123\5)\25\2\u0121\u0123\5-\27\2\u0122\u0120\3\2\2\2\u0122"+
		"\u0121\3\2\2\2\u0123\u0126\3\2\2\2\u0124\u0122\3\2\2\2\u0124\u0125\3\2"+
		"\2\2\u0125(\3\2\2\2\u0126\u0124\3\2\2\2\u0127\u0128\t\3\2\2\u0128*\3\2"+
		"\2\2\u0129\u012b\5-\27\2\u012a\u0129\3\2\2\2\u012b\u012c\3\2\2\2\u012c"+
		"\u012a\3\2\2\2\u012c\u012d\3\2\2\2\u012d,\3\2\2\2\u012e\u012f\4\62;\2"+
		"\u012f.\3\2\2\2\u0130\u0134\7=\2\2\u0131\u0133\n\4\2\2\u0132\u0131\3\2"+
		"\2\2\u0133\u0136\3\2\2\2\u0134\u0132\3\2\2\2\u0134\u0135\3\2\2\2\u0135"+
		"\u0137\3\2\2\2\u0136\u0134\3\2\2\2\u0137\u0138\b\30\2\2\u0138\60\3\2\2"+
		"\2\u0139\u013b\t\5\2\2\u013a\u0139\3\2\2\2\u013b\u013c\3\2\2\2\u013c\u013a"+
		"\3\2\2\2\u013c\u013d\3\2\2\2\u013d\u013e\3\2\2\2\u013e\u013f\b\31\2\2"+
		"\u013f\62\3\2\2\2\13\2\u009f\u00e2\u00fd\u0122\u0124\u012c\u0134\u013c"+
		"\3\b\2\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}