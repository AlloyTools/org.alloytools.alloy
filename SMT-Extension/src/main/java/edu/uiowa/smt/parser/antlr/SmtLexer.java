// Generated from Smt.g4 by ANTLR 4.7.2
package edu.uiowa.smt.parser.antlr;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.ATN;
import org.antlr.v4.runtime.atn.ATNDeserializer;
import org.antlr.v4.runtime.atn.LexerATNSimulator;
import org.antlr.v4.runtime.atn.PredictionContextCache;
import org.antlr.v4.runtime.dfa.DFA;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class SmtLexer extends Lexer
{
  static
  {
    RuntimeMetaData.checkVersion("4.7.2", RuntimeMetaData.VERSION);
  }

  protected static final DFA[] _decisionToDFA;
  protected static final PredictionContextCache _sharedContextCache =
      new PredictionContextCache();
  public static final int
      T__0 = 1, T__1 = 2, T__2 = 3, T__3 = 4, T__4 = 5, T__5 = 6, T__6 = 7, T__7 = 8, T__8 = 9,
      T__9 = 10, True = 11, False = 12, Quantifier = 13, UnaryOperator = 14, BinaryOperator = 15,
      TernaryOperator = 16, MultiArityOperator = 17, AtomPrefix = 18, UninterpretedIntPrefix = 19,
      Identifier = 20, IdentifierLetter = 21, Integer = 22, Digit = 23, Comment = 24,
      Whitespace = 25;
  public static String[] channelNames = {
      "DEFAULT_TOKEN_CHANNEL", "HIDDEN"
  };

  public static String[] modeNames = {
      "DEFAULT_MODE"
  };

  private static String[] makeRuleNames()
  {
    return new String[]{
        "T__0", "T__1", "T__2", "T__3", "T__4", "T__5", "T__6", "T__7", "T__8",
        "T__9", "True", "False", "Quantifier", "UnaryOperator", "BinaryOperator",
        "TernaryOperator", "MultiArityOperator", "AtomPrefix", "UninterpretedIntPrefix",
        "Identifier", "IdentifierLetter", "Integer", "Digit", "Comment", "Whitespace"
    };
  }

  public static final String[] ruleNames = makeRuleNames();

  private static String[] makeLiteralNames()
  {
    return new String[]{
        null, "'('", "'model'", "')'", "'declare-sort'", "'define-fun'", "'Set'",
        "'Tuple'", "'-'", "'as'", "'emptyset'", "'true'", "'false'", null, null,
        null, "'ite'", null, "'@uc_Atom_'", "'@uc_UInt_'"
    };
  }

  private static final String[] _LITERAL_NAMES = makeLiteralNames();

  private static String[] makeSymbolicNames()
  {
    return new String[]{
        null, null, null, null, null, null, null, null, null, null, null, "True",
        "False", "Quantifier", "UnaryOperator", "BinaryOperator", "TernaryOperator",
        "MultiArityOperator", "AtomPrefix", "UninterpretedIntPrefix", "Identifier",
        "IdentifierLetter", "Integer", "Digit", "Comment", "Whitespace"
    };
  }

  private static final String[] _SYMBOLIC_NAMES = makeSymbolicNames();
  public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

  /**
   * @deprecated Use {@link #VOCABULARY} instead.
   */
  @Deprecated
  public static final String[] tokenNames;

  static
  {
    tokenNames = new String[_SYMBOLIC_NAMES.length];
    for (int i = 0; i < tokenNames.length; i++)
    {
      tokenNames[i] = VOCABULARY.getLiteralName(i);
      if (tokenNames[i] == null)
      {
        tokenNames[i] = VOCABULARY.getSymbolicName(i);
      }

      if (tokenNames[i] == null)
      {
        tokenNames[i] = "<INVALID>";
      }
    }
  }

  @Override
  @Deprecated
  public String[] getTokenNames()
  {
    return tokenNames;
  }

  @Override

  public Vocabulary getVocabulary()
  {
    return VOCABULARY;
  }


  public SmtLexer(CharStream input)
  {
    super(input);
    _interp = new LexerATNSimulator(this, _ATN, _decisionToDFA, _sharedContextCache);
  }

  @Override
  public String getGrammarFileName()
  {
    return "Smt.g4";
  }

  @Override
  public String[] getRuleNames()
  {
    return ruleNames;
  }

  @Override
  public String getSerializedATN()
  {
    return _serializedATN;
  }

  @Override
  public String[] getChannelNames()
  {
    return channelNames;
  }

  @Override
  public String[] getModeNames()
  {
    return modeNames;
  }

  @Override
  public ATN getATN()
  {
    return _ATN;
  }

  public static final String _serializedATN =
      "\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2\33\u014e\b\1\4\2" +
          "\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4" +
          "\13\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22" +
          "\t\22\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31" +
          "\t\31\4\32\t\32\3\2\3\2\3\3\3\3\3\3\3\3\3\3\3\3\3\4\3\4\3\5\3\5\3\5\3" +
          "\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6" +
          "\3\6\3\6\3\6\3\7\3\7\3\7\3\7\3\b\3\b\3\b\3\b\3\b\3\b\3\t\3\t\3\n\3\n\3" +
          "\n\3\13\3\13\3\13\3\13\3\13\3\13\3\13\3\13\3\13\3\f\3\f\3\f\3\f\3\f\3" +
          "\r\3\r\3\r\3\r\3\r\3\r\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3" +
          "\16\3\16\3\16\5\16\u0087\n\16\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17" +
          "\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17" +
          "\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17\3\17" +
          "\3\17\3\17\3\17\5\17\u00b0\n\17\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20" +
          "\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20" +
          "\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20" +
          "\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20" +
          "\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\5\20\u00ee\n\20\3\21" +
          "\3\21\3\21\3\21\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22" +
          "\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\22" +
          "\3\22\5\22\u010e\n\22\3\23\3\23\3\23\3\23\3\23\3\23\3\23\3\23\3\23\3\23" +
          "\3\24\3\24\3\24\3\24\3\24\3\24\3\24\3\24\3\24\3\24\3\25\3\25\3\25\7\25" +
          "\u0127\n\25\f\25\16\25\u012a\13\25\3\25\3\25\7\25\u012e\n\25\f\25\16\25" +
          "\u0131\13\25\3\25\5\25\u0134\n\25\3\26\3\26\3\27\6\27\u0139\n\27\r\27" +
          "\16\27\u013a\3\30\3\30\3\31\3\31\7\31\u0141\n\31\f\31\16\31\u0144\13\31" +
          "\3\31\3\31\3\32\6\32\u0149\n\32\r\32\16\32\u014a\3\32\3\32\3\u012f\2\33" +
          "\3\3\5\4\7\5\t\6\13\7\r\b\17\t\21\n\23\13\25\f\27\r\31\16\33\17\35\20" +
          "\37\21!\22#\23%\24\'\25)\26+\27-\30/\31\61\32\63\33\3\2\6\5\2,-//\61\61" +
          "\t\2$$&&))/\61C\\aac|\4\2\f\f\17\17\5\2\13\f\17\17\"\"\2\u016a\2\3\3\2" +
          "\2\2\2\5\3\2\2\2\2\7\3\2\2\2\2\t\3\2\2\2\2\13\3\2\2\2\2\r\3\2\2\2\2\17" +
          "\3\2\2\2\2\21\3\2\2\2\2\23\3\2\2\2\2\25\3\2\2\2\2\27\3\2\2\2\2\31\3\2" +
          "\2\2\2\33\3\2\2\2\2\35\3\2\2\2\2\37\3\2\2\2\2!\3\2\2\2\2#\3\2\2\2\2%\3" +
          "\2\2\2\2\'\3\2\2\2\2)\3\2\2\2\2+\3\2\2\2\2-\3\2\2\2\2/\3\2\2\2\2\61\3" +
          "\2\2\2\2\63\3\2\2\2\3\65\3\2\2\2\5\67\3\2\2\2\7=\3\2\2\2\t?\3\2\2\2\13" +
          "L\3\2\2\2\rW\3\2\2\2\17[\3\2\2\2\21a\3\2\2\2\23c\3\2\2\2\25f\3\2\2\2\27" +
          "o\3\2\2\2\31t\3\2\2\2\33\u0086\3\2\2\2\35\u00af\3\2\2\2\37\u00ed\3\2\2" +
          "\2!\u00ef\3\2\2\2#\u010d\3\2\2\2%\u010f\3\2\2\2\'\u0119\3\2\2\2)\u0133" +
          "\3\2\2\2+\u0135\3\2\2\2-\u0138\3\2\2\2/\u013c\3\2\2\2\61\u013e\3\2\2\2" +
          "\63\u0148\3\2\2\2\65\66\7*\2\2\66\4\3\2\2\2\678\7o\2\289\7q\2\29:\7f\2" +
          "\2:;\7g\2\2;<\7n\2\2<\6\3\2\2\2=>\7+\2\2>\b\3\2\2\2?@\7f\2\2@A\7g\2\2" +
          "AB\7e\2\2BC\7n\2\2CD\7c\2\2DE\7t\2\2EF\7g\2\2FG\7/\2\2GH\7u\2\2HI\7q\2" +
          "\2IJ\7t\2\2JK\7v\2\2K\n\3\2\2\2LM\7f\2\2MN\7g\2\2NO\7h\2\2OP\7k\2\2PQ" +
          "\7p\2\2QR\7g\2\2RS\7/\2\2ST\7h\2\2TU\7w\2\2UV\7p\2\2V\f\3\2\2\2WX\7U\2" +
          "\2XY\7g\2\2YZ\7v\2\2Z\16\3\2\2\2[\\\7V\2\2\\]\7w\2\2]^\7r\2\2^_\7n\2\2" +
          "_`\7g\2\2`\20\3\2\2\2ab\7/\2\2b\22\3\2\2\2cd\7c\2\2de\7u\2\2e\24\3\2\2" +
          "\2fg\7g\2\2gh\7o\2\2hi\7r\2\2ij\7v\2\2jk\7{\2\2kl\7u\2\2lm\7g\2\2mn\7" +
          "v\2\2n\26\3\2\2\2op\7v\2\2pq\7t\2\2qr\7w\2\2rs\7g\2\2s\30\3\2\2\2tu\7" +
          "h\2\2uv\7c\2\2vw\7n\2\2wx\7u\2\2xy\7g\2\2y\32\3\2\2\2z{\7h\2\2{|\7q\2" +
          "\2|}\7t\2\2}~\7c\2\2~\177\7n\2\2\177\u0087\7n\2\2\u0080\u0081\7g\2\2\u0081" +
          "\u0082\7z\2\2\u0082\u0083\7k\2\2\u0083\u0084\7u\2\2\u0084\u0085\7v\2\2" +
          "\u0085\u0087\7u\2\2\u0086z\3\2\2\2\u0086\u0080\3\2\2\2\u0087\34\3\2\2" +
          "\2\u0088\u0089\7p\2\2\u0089\u008a\7q\2\2\u008a\u00b0\7v\2\2\u008b\u008c" +
          "\7u\2\2\u008c\u008d\7k\2\2\u008d\u008e\7p\2\2\u008e\u008f\7i\2\2\u008f" +
          "\u0090\7n\2\2\u0090\u0091\7g\2\2\u0091\u0092\7v\2\2\u0092\u0093\7q\2\2" +
          "\u0093\u00b0\7p\2\2\u0094\u0095\7e\2\2\u0095\u0096\7q\2\2\u0096\u0097" +
          "\7o\2\2\u0097\u0098\7r\2\2\u0098\u0099\7n\2\2\u0099\u009a\7g\2\2\u009a" +
          "\u009b\7o\2\2\u009b\u009c\7g\2\2\u009c\u009d\7p\2\2\u009d\u00b0\7v\2\2" +
          "\u009e\u009f\7v\2\2\u009f\u00a0\7t\2\2\u00a0\u00a1\7c\2\2\u00a1\u00a2" +
          "\7p\2\2\u00a2\u00a3\7u\2\2\u00a3\u00a4\7r\2\2\u00a4\u00a5\7q\2\2\u00a5" +
          "\u00a6\7u\2\2\u00a6\u00b0\7g\2\2\u00a7\u00a8\7v\2\2\u00a8\u00a9\7e\2\2" +
          "\u00a9\u00aa\7n\2\2\u00aa\u00ab\7q\2\2\u00ab\u00ac\7u\2\2\u00ac\u00ad" +
          "\7w\2\2\u00ad\u00ae\7t\2\2\u00ae\u00b0\7g\2\2\u00af\u0088\3\2\2\2\u00af" +
          "\u008b\3\2\2\2\u00af\u0094\3\2\2\2\u00af\u009e\3\2\2\2\u00af\u00a7\3\2" +
          "\2\2\u00b0\36\3\2\2\2\u00b1\u00ee\4?@\2\u00b2\u00b3\7@\2\2\u00b3\u00ee" +
          "\7?\2\2\u00b4\u00ee\7>\2\2\u00b5\u00b6\7>\2\2\u00b6\u00ee\7?\2\2\u00b7" +
          "\u00ee\t\2\2\2\u00b8\u00b9\7o\2\2\u00b9\u00ba\7q\2\2\u00ba\u00ee\7f\2" +
          "\2\u00bb\u00bc\7?\2\2\u00bc\u00ee\7@\2\2\u00bd\u00be\7w\2\2\u00be\u00bf" +
          "\7p\2\2\u00bf\u00c0\7k\2\2\u00c0\u00c1\7q\2\2\u00c1\u00ee\7p\2\2\u00c2" +
          "\u00c3\7k\2\2\u00c3\u00c4\7p\2\2\u00c4\u00c5\7v\2\2\u00c5\u00c6\7g\2\2" +
          "\u00c6\u00c7\7t\2\2\u00c7\u00c8\7u\2\2\u00c8\u00c9\7g\2\2\u00c9\u00ca" +
          "\7e\2\2\u00ca\u00cb\7v\2\2\u00cb\u00cc\7k\2\2\u00cc\u00cd\7q\2\2\u00cd" +
          "\u00ee\7p\2\2\u00ce\u00cf\7u\2\2\u00cf\u00d0\7g\2\2\u00d0\u00d1\7v\2\2" +
          "\u00d1\u00d2\7o\2\2\u00d2\u00d3\7k\2\2\u00d3\u00d4\7p\2\2\u00d4\u00d5" +
          "\7w\2\2\u00d5\u00ee\7u\2\2\u00d6\u00d7\7o\2\2\u00d7\u00d8\7g\2\2\u00d8" +
          "\u00d9\7o\2\2\u00d9\u00da\7d\2\2\u00da\u00db\7g\2\2\u00db\u00ee\7t\2\2" +
          "\u00dc\u00dd\7u\2\2\u00dd\u00de\7w\2\2\u00de\u00df\7d\2\2\u00df\u00e0" +
          "\7u\2\2\u00e0\u00e1\7g\2\2\u00e1\u00ee\7v\2\2\u00e2\u00e3\7l\2\2\u00e3" +
          "\u00e4\7q\2\2\u00e4\u00e5\7k\2\2\u00e5\u00ee\7p\2\2\u00e6\u00e7\7r\2\2" +
          "\u00e7\u00e8\7t\2\2\u00e8\u00e9\7q\2\2\u00e9\u00ea\7f\2\2\u00ea\u00eb" +
          "\7w\2\2\u00eb\u00ec\7e\2\2\u00ec\u00ee\7v\2\2\u00ed\u00b1\3\2\2\2\u00ed" +
          "\u00b2\3\2\2\2\u00ed\u00b4\3\2\2\2\u00ed\u00b5\3\2\2\2\u00ed\u00b7\3\2" +
          "\2\2\u00ed\u00b8\3\2\2\2\u00ed\u00bb\3\2\2\2\u00ed\u00bd\3\2\2\2\u00ed" +
          "\u00c2\3\2\2\2\u00ed\u00ce\3\2\2\2\u00ed\u00d6\3\2\2\2\u00ed\u00dc\3\2" +
          "\2\2\u00ed\u00e2\3\2\2\2\u00ed\u00e6\3\2\2\2\u00ee \3\2\2\2\u00ef\u00f0" +
          "\7k\2\2\u00f0\u00f1\7v\2\2\u00f1\u00f2\7g\2\2\u00f2\"\3\2\2\2\u00f3\u00f4" +
          "\7o\2\2\u00f4\u00f5\7m\2\2\u00f5\u00f6\7V\2\2\u00f6\u00f7\7w\2\2\u00f7" +
          "\u00f8\7r\2\2\u00f8\u00f9\7n\2\2\u00f9\u010e\7g\2\2\u00fa\u00fb\7k\2\2" +
          "\u00fb\u00fc\7p\2\2\u00fc\u00fd\7u\2\2\u00fd\u00fe\7g\2\2\u00fe\u00ff" +
          "\7t\2\2\u00ff\u010e\7v\2\2\u0100\u0101\7f\2\2\u0101\u0102\7k\2\2\u0102" +
          "\u0103\7u\2\2\u0103\u0104\7v\2\2\u0104\u0105\7k\2\2\u0105\u0106\7p\2\2" +
          "\u0106\u0107\7e\2\2\u0107\u010e\7v\2\2\u0108\u0109\7q\2\2\u0109\u010e" +
          "\7t\2\2\u010a\u010b\7c\2\2\u010b\u010c\7p\2\2\u010c\u010e\7f\2\2\u010d" +
          "\u00f3\3\2\2\2\u010d\u00fa\3\2\2\2\u010d\u0100\3\2\2\2\u010d\u0108\3\2" +
          "\2\2\u010d\u010a\3\2\2\2\u010e$\3\2\2\2\u010f\u0110\7B\2\2\u0110\u0111" +
          "\7w\2\2\u0111\u0112\7e\2\2\u0112\u0113\7a\2\2\u0113\u0114\7C\2\2\u0114" +
          "\u0115\7v\2\2\u0115\u0116\7q\2\2\u0116\u0117\7o\2\2\u0117\u0118\7a\2\2" +
          "\u0118&\3\2\2\2\u0119\u011a\7B\2\2\u011a\u011b\7w\2\2\u011b\u011c\7e\2" +
          "\2\u011c\u011d\7a\2\2\u011d\u011e\7W\2\2\u011e\u011f\7K\2\2\u011f\u0120" +
          "\7p\2\2\u0120\u0121\7v\2\2\u0121\u0122\7a\2\2\u0122(\3\2\2\2\u0123\u0128" +
          "\5+\26\2\u0124\u0127\5+\26\2\u0125\u0127\5/\30\2\u0126\u0124\3\2\2\2\u0126" +
          "\u0125\3\2\2\2\u0127\u012a\3\2\2\2\u0128\u0126\3\2\2\2\u0128\u0129\3\2" +
          "\2\2\u0129\u0134\3\2\2\2\u012a\u0128\3\2\2\2\u012b\u012f\7~\2\2\u012c" +
          "\u012e\13\2\2\2\u012d\u012c\3\2\2\2\u012e\u0131\3\2\2\2\u012f\u0130\3" +
          "\2\2\2\u012f\u012d\3\2\2\2\u0130\u0132\3\2\2\2\u0131\u012f\3\2\2\2\u0132" +
          "\u0134\7~\2\2\u0133\u0123\3\2\2\2\u0133\u012b\3\2\2\2\u0134*\3\2\2\2\u0135" +
          "\u0136\t\3\2\2\u0136,\3\2\2\2\u0137\u0139\5/\30\2\u0138\u0137\3\2\2\2" +
          "\u0139\u013a\3\2\2\2\u013a\u0138\3\2\2\2\u013a\u013b\3\2\2\2\u013b.\3" +
          "\2\2\2\u013c\u013d\4\62;\2\u013d\60\3\2\2\2\u013e\u0142\7=\2\2\u013f\u0141" +
          "\n\4\2\2\u0140\u013f\3\2\2\2\u0141\u0144\3\2\2\2\u0142\u0140\3\2\2\2\u0142" +
          "\u0143\3\2\2\2\u0143\u0145\3\2\2\2\u0144\u0142\3\2\2\2\u0145\u0146\b\31" +
          "\2\2\u0146\62\3\2\2\2\u0147\u0149\t\5\2\2\u0148\u0147\3\2\2\2\u0149\u014a" +
          "\3\2\2\2\u014a\u0148\3\2\2\2\u014a\u014b\3\2\2\2\u014b\u014c\3\2\2\2\u014c" +
          "\u014d\b\32\2\2\u014d\64\3\2\2\2\16\2\u0086\u00af\u00ed\u010d\u0126\u0128" +
          "\u012f\u0133\u013a\u0142\u014a\3\b\2\2";
  public static final ATN _ATN =
      new ATNDeserializer().deserialize(_serializedATN.toCharArray());

  static
  {
    _decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
    for (int i = 0; i < _ATN.getNumberOfDecisions(); i++)
    {
      _decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
    }
  }
}