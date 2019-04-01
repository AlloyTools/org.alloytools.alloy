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
		AtomPrefix=15, UnaryPrefix=16, BinaryPrefix=17, TernaryPrefix=18, Identifier=19, 
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
			"T__9", "UnaryOperator", "BinaryOperator", "TernaryOperator", "MultiArityOperator", 
			"AtomPrefix", "UnaryPrefix", "BinaryPrefix", "TernaryPrefix", "Identifier", 
			"IdentifierLetter", "Integer", "Digit", "Comment", "Whitespace"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'('", "'model'", "')'", "'declare-sort'", "'define-fun'", "'Set'", 
			"'Tuple'", "'-'", "'as'", "'emptyset'", null, null, "'ite'", null, "'@uc_Atom_'", 
			"'@uc_UnaryIntTup_'", "'@uc_BinaryIntTup_'", "'@uc_TernaryIntTup_'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, null, null, null, null, null, null, null, null, null, null, "UnaryOperator", 
			"BinaryOperator", "TernaryOperator", "MultiArityOperator", "AtomPrefix", 
			"UnaryPrefix", "BinaryPrefix", "TernaryPrefix", "Identifier", "IdentifierLetter", 
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
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2\32\u0155\b\1\4\2"+
		"\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4"+
		"\13\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22"+
		"\t\22\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31"+
		"\t\31\3\2\3\2\3\3\3\3\3\3\3\3\3\3\3\3\3\4\3\4\3\5\3\5\3\5\3\5\3\5\3\5"+
		"\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3"+
		"\6\3\7\3\7\3\7\3\7\3\b\3\b\3\b\3\b\3\b\3\b\3\t\3\t\3\n\3\n\3\n\3\13\3"+
		"\13\3\13\3\13\3\13\3\13\3\13\3\13\3\13\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f"+
		"\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3"+
		"\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\5\f\u0095\n\f\3"+
		"\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r"+
		"\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3"+
		"\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r"+
		"\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\5\r\u00d8\n\r\3\16\3"+
		"\16\3\16\3\16\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3"+
		"\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\5\17\u00f3\n\17\3\20"+
		"\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\21\3\21\3\21\3\21\3\21"+
		"\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\22\3\22"+
		"\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22"+
		"\3\22\3\22\3\23\3\23\3\23\3\23\3\23\3\23\3\23\3\23\3\23\3\23\3\23\3\23"+
		"\3\23\3\23\3\23\3\23\3\23\3\23\3\23\3\24\3\24\3\24\7\24\u0138\n\24\f\24"+
		"\16\24\u013b\13\24\3\25\3\25\3\26\6\26\u0140\n\26\r\26\16\26\u0141\3\27"+
		"\3\27\3\30\3\30\7\30\u0148\n\30\f\30\16\30\u014b\13\30\3\30\3\30\3\31"+
		"\6\31\u0150\n\31\r\31\16\31\u0151\3\31\3\31\2\2\32\3\3\5\4\7\5\t\6\13"+
		"\7\r\b\17\t\21\n\23\13\25\f\27\r\31\16\33\17\35\20\37\21!\22#\23%\24\'"+
		"\25)\26+\27-\30/\31\61\32\3\2\6\5\2,-//\61\61\5\2C\\aac|\4\2\f\f\17\17"+
		"\5\2\13\f\17\17\"\"\2\u016e\2\3\3\2\2\2\2\5\3\2\2\2\2\7\3\2\2\2\2\t\3"+
		"\2\2\2\2\13\3\2\2\2\2\r\3\2\2\2\2\17\3\2\2\2\2\21\3\2\2\2\2\23\3\2\2\2"+
		"\2\25\3\2\2\2\2\27\3\2\2\2\2\31\3\2\2\2\2\33\3\2\2\2\2\35\3\2\2\2\2\37"+
		"\3\2\2\2\2!\3\2\2\2\2#\3\2\2\2\2%\3\2\2\2\2\'\3\2\2\2\2)\3\2\2\2\2+\3"+
		"\2\2\2\2-\3\2\2\2\2/\3\2\2\2\2\61\3\2\2\2\3\63\3\2\2\2\5\65\3\2\2\2\7"+
		";\3\2\2\2\t=\3\2\2\2\13J\3\2\2\2\rU\3\2\2\2\17Y\3\2\2\2\21_\3\2\2\2\23"+
		"a\3\2\2\2\25d\3\2\2\2\27\u0094\3\2\2\2\31\u00d7\3\2\2\2\33\u00d9\3\2\2"+
		"\2\35\u00f2\3\2\2\2\37\u00f4\3\2\2\2!\u00fe\3\2\2\2#\u010f\3\2\2\2%\u0121"+
		"\3\2\2\2\'\u0134\3\2\2\2)\u013c\3\2\2\2+\u013f\3\2\2\2-\u0143\3\2\2\2"+
		"/\u0145\3\2\2\2\61\u014f\3\2\2\2\63\64\7*\2\2\64\4\3\2\2\2\65\66\7o\2"+
		"\2\66\67\7q\2\2\678\7f\2\289\7g\2\29:\7n\2\2:\6\3\2\2\2;<\7+\2\2<\b\3"+
		"\2\2\2=>\7f\2\2>?\7g\2\2?@\7e\2\2@A\7n\2\2AB\7c\2\2BC\7t\2\2CD\7g\2\2"+
		"DE\7/\2\2EF\7u\2\2FG\7q\2\2GH\7t\2\2HI\7v\2\2I\n\3\2\2\2JK\7f\2\2KL\7"+
		"g\2\2LM\7h\2\2MN\7k\2\2NO\7p\2\2OP\7g\2\2PQ\7/\2\2QR\7h\2\2RS\7w\2\2S"+
		"T\7p\2\2T\f\3\2\2\2UV\7U\2\2VW\7g\2\2WX\7v\2\2X\16\3\2\2\2YZ\7V\2\2Z["+
		"\7w\2\2[\\\7r\2\2\\]\7n\2\2]^\7g\2\2^\20\3\2\2\2_`\7/\2\2`\22\3\2\2\2"+
		"ab\7c\2\2bc\7u\2\2c\24\3\2\2\2de\7g\2\2ef\7o\2\2fg\7r\2\2gh\7v\2\2hi\7"+
		"{\2\2ij\7u\2\2jk\7g\2\2kl\7v\2\2l\26\3\2\2\2mn\7p\2\2no\7q\2\2o\u0095"+
		"\7v\2\2pq\7u\2\2qr\7k\2\2rs\7p\2\2st\7i\2\2tu\7n\2\2uv\7g\2\2vw\7v\2\2"+
		"wx\7q\2\2x\u0095\7p\2\2yz\7e\2\2z{\7q\2\2{|\7o\2\2|}\7r\2\2}~\7n\2\2~"+
		"\177\7g\2\2\177\u0080\7o\2\2\u0080\u0081\7g\2\2\u0081\u0082\7p\2\2\u0082"+
		"\u0095\7v\2\2\u0083\u0084\7v\2\2\u0084\u0085\7t\2\2\u0085\u0086\7c\2\2"+
		"\u0086\u0087\7p\2\2\u0087\u0088\7u\2\2\u0088\u0089\7r\2\2\u0089\u008a"+
		"\7q\2\2\u008a\u008b\7u\2\2\u008b\u0095\7g\2\2\u008c\u008d\7v\2\2\u008d"+
		"\u008e\7e\2\2\u008e\u008f\7n\2\2\u008f\u0090\7q\2\2\u0090\u0091\7u\2\2"+
		"\u0091\u0092\7w\2\2\u0092\u0093\7t\2\2\u0093\u0095\7g\2\2\u0094m\3\2\2"+
		"\2\u0094p\3\2\2\2\u0094y\3\2\2\2\u0094\u0083\3\2\2\2\u0094\u008c\3\2\2"+
		"\2\u0095\30\3\2\2\2\u0096\u00d8\4?@\2\u0097\u0098\7@\2\2\u0098\u00d8\7"+
		"?\2\2\u0099\u00d8\7>\2\2\u009a\u009b\7>\2\2\u009b\u00d8\7?\2\2\u009c\u00d8"+
		"\t\2\2\2\u009d\u009e\7o\2\2\u009e\u009f\7q\2\2\u009f\u00d8\7f\2\2\u00a0"+
		"\u00a1\7q\2\2\u00a1\u00d8\7t\2\2\u00a2\u00a3\7c\2\2\u00a3\u00a4\7p\2\2"+
		"\u00a4\u00d8\7f\2\2\u00a5\u00a6\7?\2\2\u00a6\u00d8\7@\2\2\u00a7\u00a8"+
		"\7w\2\2\u00a8\u00a9\7p\2\2\u00a9\u00aa\7k\2\2\u00aa\u00ab\7q\2\2\u00ab"+
		"\u00d8\7p\2\2\u00ac\u00ad\7k\2\2\u00ad\u00ae\7p\2\2\u00ae\u00af\7v\2\2"+
		"\u00af\u00b0\7g\2\2\u00b0\u00b1\7t\2\2\u00b1\u00b2\7u\2\2\u00b2\u00b3"+
		"\7g\2\2\u00b3\u00b4\7e\2\2\u00b4\u00b5\7v\2\2\u00b5\u00b6\7k\2\2\u00b6"+
		"\u00b7\7q\2\2\u00b7\u00d8\7p\2\2\u00b8\u00b9\7u\2\2\u00b9\u00ba\7g\2\2"+
		"\u00ba\u00bb\7v\2\2\u00bb\u00bc\7o\2\2\u00bc\u00bd\7k\2\2\u00bd\u00be"+
		"\7p\2\2\u00be\u00bf\7w\2\2\u00bf\u00d8\7u\2\2\u00c0\u00c1\7o\2\2\u00c1"+
		"\u00c2\7g\2\2\u00c2\u00c3\7o\2\2\u00c3\u00c4\7d\2\2\u00c4\u00c5\7g\2\2"+
		"\u00c5\u00d8\7t\2\2\u00c6\u00c7\7u\2\2\u00c7\u00c8\7w\2\2\u00c8\u00c9"+
		"\7d\2\2\u00c9\u00ca\7u\2\2\u00ca\u00cb\7g\2\2\u00cb\u00d8\7v\2\2\u00cc"+
		"\u00cd\7l\2\2\u00cd\u00ce\7q\2\2\u00ce\u00cf\7k\2\2\u00cf\u00d8\7p\2\2"+
		"\u00d0\u00d1\7r\2\2\u00d1\u00d2\7t\2\2\u00d2\u00d3\7q\2\2\u00d3\u00d4"+
		"\7f\2\2\u00d4\u00d5\7w\2\2\u00d5\u00d6\7e\2\2\u00d6\u00d8\7v\2\2\u00d7"+
		"\u0096\3\2\2\2\u00d7\u0097\3\2\2\2\u00d7\u0099\3\2\2\2\u00d7\u009a\3\2"+
		"\2\2\u00d7\u009c\3\2\2\2\u00d7\u009d\3\2\2\2\u00d7\u00a0\3\2\2\2\u00d7"+
		"\u00a2\3\2\2\2\u00d7\u00a5\3\2\2\2\u00d7\u00a7\3\2\2\2\u00d7\u00ac\3\2"+
		"\2\2\u00d7\u00b8\3\2\2\2\u00d7\u00c0\3\2\2\2\u00d7\u00c6\3\2\2\2\u00d7"+
		"\u00cc\3\2\2\2\u00d7\u00d0\3\2\2\2\u00d8\32\3\2\2\2\u00d9\u00da\7k\2\2"+
		"\u00da\u00db\7v\2\2\u00db\u00dc\7g\2\2\u00dc\34\3\2\2\2\u00dd\u00de\7"+
		"o\2\2\u00de\u00df\7m\2\2\u00df\u00e0\7V\2\2\u00e0\u00e1\7w\2\2\u00e1\u00e2"+
		"\7r\2\2\u00e2\u00e3\7n\2\2\u00e3\u00f3\7g\2\2\u00e4\u00e5\7k\2\2\u00e5"+
		"\u00e6\7p\2\2\u00e6\u00e7\7u\2\2\u00e7\u00e8\7g\2\2\u00e8\u00e9\7t\2\2"+
		"\u00e9\u00f3\7v\2\2\u00ea\u00eb\7f\2\2\u00eb\u00ec\7k\2\2\u00ec\u00ed"+
		"\7u\2\2\u00ed\u00ee\7v\2\2\u00ee\u00ef\7k\2\2\u00ef\u00f0\7p\2\2\u00f0"+
		"\u00f1\7e\2\2\u00f1\u00f3\7v\2\2\u00f2\u00dd\3\2\2\2\u00f2\u00e4\3\2\2"+
		"\2\u00f2\u00ea\3\2\2\2\u00f3\36\3\2\2\2\u00f4\u00f5\7B\2\2\u00f5\u00f6"+
		"\7w\2\2\u00f6\u00f7\7e\2\2\u00f7\u00f8\7a\2\2\u00f8\u00f9\7C\2\2\u00f9"+
		"\u00fa\7v\2\2\u00fa\u00fb\7q\2\2\u00fb\u00fc\7o\2\2\u00fc\u00fd\7a\2\2"+
		"\u00fd \3\2\2\2\u00fe\u00ff\7B\2\2\u00ff\u0100\7w\2\2\u0100\u0101\7e\2"+
		"\2\u0101\u0102\7a\2\2\u0102\u0103\7W\2\2\u0103\u0104\7p\2\2\u0104\u0105"+
		"\7c\2\2\u0105\u0106\7t\2\2\u0106\u0107\7{\2\2\u0107\u0108\7K\2\2\u0108"+
		"\u0109\7p\2\2\u0109\u010a\7v\2\2\u010a\u010b\7V\2\2\u010b\u010c\7w\2\2"+
		"\u010c\u010d\7r\2\2\u010d\u010e\7a\2\2\u010e\"\3\2\2\2\u010f\u0110\7B"+
		"\2\2\u0110\u0111\7w\2\2\u0111\u0112\7e\2\2\u0112\u0113\7a\2\2\u0113\u0114"+
		"\7D\2\2\u0114\u0115\7k\2\2\u0115\u0116\7p\2\2\u0116\u0117\7c\2\2\u0117"+
		"\u0118\7t\2\2\u0118\u0119\7{\2\2\u0119\u011a\7K\2\2\u011a\u011b\7p\2\2"+
		"\u011b\u011c\7v\2\2\u011c\u011d\7V\2\2\u011d\u011e\7w\2\2\u011e\u011f"+
		"\7r\2\2\u011f\u0120\7a\2\2\u0120$\3\2\2\2\u0121\u0122\7B\2\2\u0122\u0123"+
		"\7w\2\2\u0123\u0124\7e\2\2\u0124\u0125\7a\2\2\u0125\u0126\7V\2\2\u0126"+
		"\u0127\7g\2\2\u0127\u0128\7t\2\2\u0128\u0129\7p\2\2\u0129\u012a\7c\2\2"+
		"\u012a\u012b\7t\2\2\u012b\u012c\7{\2\2\u012c\u012d\7K\2\2\u012d\u012e"+
		"\7p\2\2\u012e\u012f\7v\2\2\u012f\u0130\7V\2\2\u0130\u0131\7w\2\2\u0131"+
		"\u0132\7r\2\2\u0132\u0133\7a\2\2\u0133&\3\2\2\2\u0134\u0139\5)\25\2\u0135"+
		"\u0138\5)\25\2\u0136\u0138\5-\27\2\u0137\u0135\3\2\2\2\u0137\u0136\3\2"+
		"\2\2\u0138\u013b\3\2\2\2\u0139\u0137\3\2\2\2\u0139\u013a\3\2\2\2\u013a"+
		"(\3\2\2\2\u013b\u0139\3\2\2\2\u013c\u013d\t\3\2\2\u013d*\3\2\2\2\u013e"+
		"\u0140\5-\27\2\u013f\u013e\3\2\2\2\u0140\u0141\3\2\2\2\u0141\u013f\3\2"+
		"\2\2\u0141\u0142\3\2\2\2\u0142,\3\2\2\2\u0143\u0144\4\62;\2\u0144.\3\2"+
		"\2\2\u0145\u0149\7=\2\2\u0146\u0148\n\4\2\2\u0147\u0146\3\2\2\2\u0148"+
		"\u014b\3\2\2\2\u0149\u0147\3\2\2\2\u0149\u014a\3\2\2\2\u014a\u014c\3\2"+
		"\2\2\u014b\u0149\3\2\2\2\u014c\u014d\b\30\2\2\u014d\60\3\2\2\2\u014e\u0150"+
		"\t\5\2\2\u014f\u014e\3\2\2\2\u0150\u0151\3\2\2\2\u0151\u014f\3\2\2\2\u0151"+
		"\u0152\3\2\2\2\u0152\u0153\3\2\2\2\u0153\u0154\b\31\2\2\u0154\62\3\2\2"+
		"\2\13\2\u0094\u00d7\u00f2\u0137\u0139\u0141\u0149\u0151\3\b\2\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}