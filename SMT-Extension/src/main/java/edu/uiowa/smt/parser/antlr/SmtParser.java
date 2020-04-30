// Generated from Smt.g4 by ANTLR 4.7.2
package edu.uiowa.smt.parser.antlr;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.ATN;
import org.antlr.v4.runtime.atn.ATNDeserializer;
import org.antlr.v4.runtime.atn.ParserATNSimulator;
import org.antlr.v4.runtime.atn.PredictionContextCache;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.tree.ParseTreeListener;
import org.antlr.v4.runtime.tree.ParseTreeVisitor;
import org.antlr.v4.runtime.tree.TerminalNode;

import java.util.List;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class SmtParser extends Parser
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
  public static final int
      RULE_model = 0, RULE_sortDeclaration = 1, RULE_functionDefinition = 2,
      RULE_variableDeclaration = 3, RULE_sort = 4, RULE_setSort = 5, RULE_tupleSort = 6,
      RULE_sortName = 7, RULE_arity = 8, RULE_functionName = 9, RULE_variableName = 10,
      RULE_expression = 11, RULE_unaryExpression = 12, RULE_binaryExpression = 13,
      RULE_ternaryExpression = 14, RULE_multiArityExpression = 15, RULE_quantifiedExpression = 16,
      RULE_functionCallExpression = 17, RULE_variable = 18, RULE_constant = 19,
      RULE_boolConstant = 20, RULE_integerConstant = 21, RULE_uninterpretedConstant = 22,
      RULE_emptySet = 23, RULE_getValue = 24, RULE_getUnsatCore = 25;

  private static String[] makeRuleNames()
  {
    return new String[]{
        "model", "sortDeclaration", "functionDefinition", "variableDeclaration",
        "sort", "setSort", "tupleSort", "sortName", "arity", "functionName",
        "variableName", "expression", "unaryExpression", "binaryExpression",
        "ternaryExpression", "multiArityExpression", "quantifiedExpression",
        "functionCallExpression", "variable", "constant", "boolConstant", "integerConstant",
        "uninterpretedConstant", "emptySet", "getValue", "getUnsatCore"
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
  public ATN getATN()
  {
    return _ATN;
  }

  public SmtParser(TokenStream input)
  {
    super(input);
    _interp = new ParserATNSimulator(this, _ATN, _decisionToDFA, _sharedContextCache);
  }

  public static class ModelContext extends ParserRuleContext
  {
    public List<SortDeclarationContext> sortDeclaration()
    {
      return getRuleContexts(SortDeclarationContext.class);
    }

    public SortDeclarationContext sortDeclaration(int i)
    {
      return getRuleContext(SortDeclarationContext.class, i);
    }

    public List<FunctionDefinitionContext> functionDefinition()
    {
      return getRuleContexts(FunctionDefinitionContext.class);
    }

    public FunctionDefinitionContext functionDefinition(int i)
    {
      return getRuleContext(FunctionDefinitionContext.class, i);
    }

    public ModelContext(ParserRuleContext parent, int invokingState)
    {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex()
    {
      return RULE_model;
    }

    @Override
    public void enterRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).enterModel(this);
      }
    }

    @Override
    public void exitRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).exitModel(this);
      }
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor)
    {
      if (visitor instanceof SmtVisitor)
      {
        return ((SmtVisitor<? extends T>) visitor).visitModel(this);
      }
      else
      {
        return visitor.visitChildren(this);
      }
    }
  }

  public final ModelContext model() throws RecognitionException
  {
    ModelContext _localctx = new ModelContext(_ctx, getState());
    enterRule(_localctx, 0, RULE_model);
    int _la;
    try
    {
      int _alt;
      enterOuterAlt(_localctx, 1);
      {
        setState(52);
        match(T__0);
        setState(53);
        match(T__1);
        setState(57);
        _errHandler.sync(this);
        _alt = getInterpreter().adaptivePredict(_input, 0, _ctx);
        while (_alt != 2 && _alt != org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER)
        {
          if (_alt == 1)
          {
            {
              {
                setState(54);
                sortDeclaration();
              }
            }
          }
          setState(59);
          _errHandler.sync(this);
          _alt = getInterpreter().adaptivePredict(_input, 0, _ctx);
        }
        setState(63);
        _errHandler.sync(this);
        _la = _input.LA(1);
        while (_la == T__0)
        {
          {
            {
              setState(60);
              functionDefinition();
            }
          }
          setState(65);
          _errHandler.sync(this);
          _la = _input.LA(1);
        }
        setState(66);
        match(T__2);
      }
    }
    catch (RecognitionException re)
    {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    }
    finally
    {
      exitRule();
    }
    return _localctx;
  }

  public static class SortDeclarationContext extends ParserRuleContext
  {
    public SortNameContext sortName()
    {
      return getRuleContext(SortNameContext.class, 0);
    }

    public ArityContext arity()
    {
      return getRuleContext(ArityContext.class, 0);
    }

    public SortDeclarationContext(ParserRuleContext parent, int invokingState)
    {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex()
    {
      return RULE_sortDeclaration;
    }

    @Override
    public void enterRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).enterSortDeclaration(this);
      }
    }

    @Override
    public void exitRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).exitSortDeclaration(this);
      }
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor)
    {
      if (visitor instanceof SmtVisitor)
      {
        return ((SmtVisitor<? extends T>) visitor).visitSortDeclaration(this);
      }
      else
      {
        return visitor.visitChildren(this);
      }
    }
  }

  public final SortDeclarationContext sortDeclaration() throws RecognitionException
  {
    SortDeclarationContext _localctx = new SortDeclarationContext(_ctx, getState());
    enterRule(_localctx, 2, RULE_sortDeclaration);
    try
    {
      enterOuterAlt(_localctx, 1);
      {
        setState(68);
        match(T__0);
        setState(69);
        match(T__3);
        setState(70);
        sortName();
        setState(71);
        arity();
        setState(72);
        match(T__2);
      }
    }
    catch (RecognitionException re)
    {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    }
    finally
    {
      exitRule();
    }
    return _localctx;
  }

  public static class FunctionDefinitionContext extends ParserRuleContext
  {
    public FunctionNameContext functionName()
    {
      return getRuleContext(FunctionNameContext.class, 0);
    }

    public SortContext sort()
    {
      return getRuleContext(SortContext.class, 0);
    }

    public ExpressionContext expression()
    {
      return getRuleContext(ExpressionContext.class, 0);
    }

    public List<VariableDeclarationContext> variableDeclaration()
    {
      return getRuleContexts(VariableDeclarationContext.class);
    }

    public VariableDeclarationContext variableDeclaration(int i)
    {
      return getRuleContext(VariableDeclarationContext.class, i);
    }

    public FunctionDefinitionContext(ParserRuleContext parent, int invokingState)
    {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex()
    {
      return RULE_functionDefinition;
    }

    @Override
    public void enterRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).enterFunctionDefinition(this);
      }
    }

    @Override
    public void exitRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).exitFunctionDefinition(this);
      }
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor)
    {
      if (visitor instanceof SmtVisitor)
      {
        return ((SmtVisitor<? extends T>) visitor).visitFunctionDefinition(this);
      }
      else
      {
        return visitor.visitChildren(this);
      }
    }
  }

  public final FunctionDefinitionContext functionDefinition() throws RecognitionException
  {
    FunctionDefinitionContext _localctx = new FunctionDefinitionContext(_ctx, getState());
    enterRule(_localctx, 4, RULE_functionDefinition);
    int _la;
    try
    {
      enterOuterAlt(_localctx, 1);
      {
        setState(74);
        match(T__0);
        setState(75);
        match(T__4);
        setState(76);
        functionName();
        setState(77);
        match(T__0);
        setState(81);
        _errHandler.sync(this);
        _la = _input.LA(1);
        while (_la == T__0)
        {
          {
            {
              setState(78);
              variableDeclaration();
            }
          }
          setState(83);
          _errHandler.sync(this);
          _la = _input.LA(1);
        }
        setState(84);
        match(T__2);
        setState(85);
        sort();
        setState(86);
        expression();
        setState(87);
        match(T__2);
      }
    }
    catch (RecognitionException re)
    {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    }
    finally
    {
      exitRule();
    }
    return _localctx;
  }

  public static class VariableDeclarationContext extends ParserRuleContext
  {
    public VariableNameContext variableName()
    {
      return getRuleContext(VariableNameContext.class, 0);
    }

    public SortContext sort()
    {
      return getRuleContext(SortContext.class, 0);
    }

    public VariableDeclarationContext(ParserRuleContext parent, int invokingState)
    {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex()
    {
      return RULE_variableDeclaration;
    }

    @Override
    public void enterRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).enterVariableDeclaration(this);
      }
    }

    @Override
    public void exitRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).exitVariableDeclaration(this);
      }
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor)
    {
      if (visitor instanceof SmtVisitor)
      {
        return ((SmtVisitor<? extends T>) visitor).visitVariableDeclaration(this);
      }
      else
      {
        return visitor.visitChildren(this);
      }
    }
  }

  public final VariableDeclarationContext variableDeclaration() throws RecognitionException
  {
    VariableDeclarationContext _localctx = new VariableDeclarationContext(_ctx, getState());
    enterRule(_localctx, 6, RULE_variableDeclaration);
    try
    {
      enterOuterAlt(_localctx, 1);
      {
        setState(89);
        match(T__0);
        setState(90);
        variableName();
        setState(91);
        sort();
        setState(92);
        match(T__2);
      }
    }
    catch (RecognitionException re)
    {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    }
    finally
    {
      exitRule();
    }
    return _localctx;
  }

  public static class SortContext extends ParserRuleContext
  {
    public SortNameContext sortName()
    {
      return getRuleContext(SortNameContext.class, 0);
    }

    public TupleSortContext tupleSort()
    {
      return getRuleContext(TupleSortContext.class, 0);
    }

    public SetSortContext setSort()
    {
      return getRuleContext(SetSortContext.class, 0);
    }

    public SortContext(ParserRuleContext parent, int invokingState)
    {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex()
    {
      return RULE_sort;
    }

    @Override
    public void enterRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).enterSort(this);
      }
    }

    @Override
    public void exitRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).exitSort(this);
      }
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor)
    {
      if (visitor instanceof SmtVisitor)
      {
        return ((SmtVisitor<? extends T>) visitor).visitSort(this);
      }
      else
      {
        return visitor.visitChildren(this);
      }
    }
  }

  public final SortContext sort() throws RecognitionException
  {
    SortContext _localctx = new SortContext(_ctx, getState());
    enterRule(_localctx, 8, RULE_sort);
    try
    {
      setState(103);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 3, _ctx))
      {
        case 1:
          enterOuterAlt(_localctx, 1);
        {
          setState(94);
          sortName();
        }
        break;
        case 2:
          enterOuterAlt(_localctx, 2);
        {
          setState(95);
          match(T__0);
          setState(96);
          tupleSort();
          setState(97);
          match(T__2);
        }
        break;
        case 3:
          enterOuterAlt(_localctx, 3);
        {
          setState(99);
          match(T__0);
          setState(100);
          setSort();
          setState(101);
          match(T__2);
        }
        break;
      }
    }
    catch (RecognitionException re)
    {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    }
    finally
    {
      exitRule();
    }
    return _localctx;
  }

  public static class SetSortContext extends ParserRuleContext
  {
    public SortContext sort()
    {
      return getRuleContext(SortContext.class, 0);
    }

    public SetSortContext(ParserRuleContext parent, int invokingState)
    {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex()
    {
      return RULE_setSort;
    }

    @Override
    public void enterRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).enterSetSort(this);
      }
    }

    @Override
    public void exitRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).exitSetSort(this);
      }
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor)
    {
      if (visitor instanceof SmtVisitor)
      {
        return ((SmtVisitor<? extends T>) visitor).visitSetSort(this);
      }
      else
      {
        return visitor.visitChildren(this);
      }
    }
  }

  public final SetSortContext setSort() throws RecognitionException
  {
    SetSortContext _localctx = new SetSortContext(_ctx, getState());
    enterRule(_localctx, 10, RULE_setSort);
    try
    {
      enterOuterAlt(_localctx, 1);
      {
        setState(105);
        match(T__5);
        setState(106);
        sort();
      }
    }
    catch (RecognitionException re)
    {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    }
    finally
    {
      exitRule();
    }
    return _localctx;
  }

  public static class TupleSortContext extends ParserRuleContext
  {
    public List<SortContext> sort()
    {
      return getRuleContexts(SortContext.class);
    }

    public SortContext sort(int i)
    {
      return getRuleContext(SortContext.class, i);
    }

    public TupleSortContext(ParserRuleContext parent, int invokingState)
    {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex()
    {
      return RULE_tupleSort;
    }

    @Override
    public void enterRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).enterTupleSort(this);
      }
    }

    @Override
    public void exitRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).exitTupleSort(this);
      }
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor)
    {
      if (visitor instanceof SmtVisitor)
      {
        return ((SmtVisitor<? extends T>) visitor).visitTupleSort(this);
      }
      else
      {
        return visitor.visitChildren(this);
      }
    }
  }

  public final TupleSortContext tupleSort() throws RecognitionException
  {
    TupleSortContext _localctx = new TupleSortContext(_ctx, getState());
    enterRule(_localctx, 12, RULE_tupleSort);
    int _la;
    try
    {
      enterOuterAlt(_localctx, 1);
      {
        setState(108);
        match(T__6);
        setState(110);
        _errHandler.sync(this);
        _la = _input.LA(1);
        do
        {
          {
            {
              setState(109);
              sort();
            }
          }
          setState(112);
          _errHandler.sync(this);
          _la = _input.LA(1);
        } while (_la == T__0 || _la == Identifier);
      }
    }
    catch (RecognitionException re)
    {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    }
    finally
    {
      exitRule();
    }
    return _localctx;
  }

  public static class SortNameContext extends ParserRuleContext
  {
    public TerminalNode Identifier()
    {
      return getToken(SmtParser.Identifier, 0);
    }

    public SortNameContext(ParserRuleContext parent, int invokingState)
    {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex()
    {
      return RULE_sortName;
    }

    @Override
    public void enterRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).enterSortName(this);
      }
    }

    @Override
    public void exitRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).exitSortName(this);
      }
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor)
    {
      if (visitor instanceof SmtVisitor)
      {
        return ((SmtVisitor<? extends T>) visitor).visitSortName(this);
      }
      else
      {
        return visitor.visitChildren(this);
      }
    }
  }

  public final SortNameContext sortName() throws RecognitionException
  {
    SortNameContext _localctx = new SortNameContext(_ctx, getState());
    enterRule(_localctx, 14, RULE_sortName);
    try
    {
      enterOuterAlt(_localctx, 1);
      {
        setState(114);
        match(Identifier);
      }
    }
    catch (RecognitionException re)
    {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    }
    finally
    {
      exitRule();
    }
    return _localctx;
  }

  public static class ArityContext extends ParserRuleContext
  {
    public TerminalNode Integer()
    {
      return getToken(SmtParser.Integer, 0);
    }

    public ArityContext(ParserRuleContext parent, int invokingState)
    {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex()
    {
      return RULE_arity;
    }

    @Override
    public void enterRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).enterArity(this);
      }
    }

    @Override
    public void exitRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).exitArity(this);
      }
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor)
    {
      if (visitor instanceof SmtVisitor)
      {
        return ((SmtVisitor<? extends T>) visitor).visitArity(this);
      }
      else
      {
        return visitor.visitChildren(this);
      }
    }
  }

  public final ArityContext arity() throws RecognitionException
  {
    ArityContext _localctx = new ArityContext(_ctx, getState());
    enterRule(_localctx, 16, RULE_arity);
    try
    {
      enterOuterAlt(_localctx, 1);
      {
        setState(116);
        match(Integer);
      }
    }
    catch (RecognitionException re)
    {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    }
    finally
    {
      exitRule();
    }
    return _localctx;
  }

  public static class FunctionNameContext extends ParserRuleContext
  {
    public TerminalNode Identifier()
    {
      return getToken(SmtParser.Identifier, 0);
    }

    public FunctionNameContext(ParserRuleContext parent, int invokingState)
    {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex()
    {
      return RULE_functionName;
    }

    @Override
    public void enterRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).enterFunctionName(this);
      }
    }

    @Override
    public void exitRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).exitFunctionName(this);
      }
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor)
    {
      if (visitor instanceof SmtVisitor)
      {
        return ((SmtVisitor<? extends T>) visitor).visitFunctionName(this);
      }
      else
      {
        return visitor.visitChildren(this);
      }
    }
  }

  public final FunctionNameContext functionName() throws RecognitionException
  {
    FunctionNameContext _localctx = new FunctionNameContext(_ctx, getState());
    enterRule(_localctx, 18, RULE_functionName);
    try
    {
      enterOuterAlt(_localctx, 1);
      {
        setState(118);
        match(Identifier);
      }
    }
    catch (RecognitionException re)
    {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    }
    finally
    {
      exitRule();
    }
    return _localctx;
  }

  public static class VariableNameContext extends ParserRuleContext
  {
    public TerminalNode Identifier()
    {
      return getToken(SmtParser.Identifier, 0);
    }

    public VariableNameContext(ParserRuleContext parent, int invokingState)
    {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex()
    {
      return RULE_variableName;
    }

    @Override
    public void enterRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).enterVariableName(this);
      }
    }

    @Override
    public void exitRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).exitVariableName(this);
      }
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor)
    {
      if (visitor instanceof SmtVisitor)
      {
        return ((SmtVisitor<? extends T>) visitor).visitVariableName(this);
      }
      else
      {
        return visitor.visitChildren(this);
      }
    }
  }

  public final VariableNameContext variableName() throws RecognitionException
  {
    VariableNameContext _localctx = new VariableNameContext(_ctx, getState());
    enterRule(_localctx, 20, RULE_variableName);
    try
    {
      enterOuterAlt(_localctx, 1);
      {
        setState(120);
        match(Identifier);
      }
    }
    catch (RecognitionException re)
    {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    }
    finally
    {
      exitRule();
    }
    return _localctx;
  }

  public static class ExpressionContext extends ParserRuleContext
  {
    public ConstantContext constant()
    {
      return getRuleContext(ConstantContext.class, 0);
    }

    public VariableContext variable()
    {
      return getRuleContext(VariableContext.class, 0);
    }

    public UnaryExpressionContext unaryExpression()
    {
      return getRuleContext(UnaryExpressionContext.class, 0);
    }

    public BinaryExpressionContext binaryExpression()
    {
      return getRuleContext(BinaryExpressionContext.class, 0);
    }

    public TernaryExpressionContext ternaryExpression()
    {
      return getRuleContext(TernaryExpressionContext.class, 0);
    }

    public MultiArityExpressionContext multiArityExpression()
    {
      return getRuleContext(MultiArityExpressionContext.class, 0);
    }

    public QuantifiedExpressionContext quantifiedExpression()
    {
      return getRuleContext(QuantifiedExpressionContext.class, 0);
    }

    public FunctionCallExpressionContext functionCallExpression()
    {
      return getRuleContext(FunctionCallExpressionContext.class, 0);
    }

    public ExpressionContext expression()
    {
      return getRuleContext(ExpressionContext.class, 0);
    }

    public ExpressionContext(ParserRuleContext parent, int invokingState)
    {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex()
    {
      return RULE_expression;
    }

    @Override
    public void enterRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).enterExpression(this);
      }
    }

    @Override
    public void exitRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).exitExpression(this);
      }
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor)
    {
      if (visitor instanceof SmtVisitor)
      {
        return ((SmtVisitor<? extends T>) visitor).visitExpression(this);
      }
      else
      {
        return visitor.visitChildren(this);
      }
    }
  }

  public final ExpressionContext expression() throws RecognitionException
  {
    ExpressionContext _localctx = new ExpressionContext(_ctx, getState());
    enterRule(_localctx, 22, RULE_expression);
    try
    {
      setState(134);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 5, _ctx))
      {
        case 1:
          enterOuterAlt(_localctx, 1);
        {
          setState(122);
          constant();
        }
        break;
        case 2:
          enterOuterAlt(_localctx, 2);
        {
          setState(123);
          variable();
        }
        break;
        case 3:
          enterOuterAlt(_localctx, 3);
        {
          setState(124);
          unaryExpression();
        }
        break;
        case 4:
          enterOuterAlt(_localctx, 4);
        {
          setState(125);
          binaryExpression();
        }
        break;
        case 5:
          enterOuterAlt(_localctx, 5);
        {
          setState(126);
          ternaryExpression();
        }
        break;
        case 6:
          enterOuterAlt(_localctx, 6);
        {
          setState(127);
          multiArityExpression();
        }
        break;
        case 7:
          enterOuterAlt(_localctx, 7);
        {
          setState(128);
          quantifiedExpression();
        }
        break;
        case 8:
          enterOuterAlt(_localctx, 8);
        {
          setState(129);
          functionCallExpression();
        }
        break;
        case 9:
          enterOuterAlt(_localctx, 9);
        {
          setState(130);
          match(T__0);
          setState(131);
          expression();
          setState(132);
          match(T__2);
        }
        break;
      }
    }
    catch (RecognitionException re)
    {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    }
    finally
    {
      exitRule();
    }
    return _localctx;
  }

  public static class UnaryExpressionContext extends ParserRuleContext
  {
    public TerminalNode UnaryOperator()
    {
      return getToken(SmtParser.UnaryOperator, 0);
    }

    public ExpressionContext expression()
    {
      return getRuleContext(ExpressionContext.class, 0);
    }

    public UnaryExpressionContext(ParserRuleContext parent, int invokingState)
    {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex()
    {
      return RULE_unaryExpression;
    }

    @Override
    public void enterRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).enterUnaryExpression(this);
      }
    }

    @Override
    public void exitRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).exitUnaryExpression(this);
      }
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor)
    {
      if (visitor instanceof SmtVisitor)
      {
        return ((SmtVisitor<? extends T>) visitor).visitUnaryExpression(this);
      }
      else
      {
        return visitor.visitChildren(this);
      }
    }
  }

  public final UnaryExpressionContext unaryExpression() throws RecognitionException
  {
    UnaryExpressionContext _localctx = new UnaryExpressionContext(_ctx, getState());
    enterRule(_localctx, 24, RULE_unaryExpression);
    try
    {
      enterOuterAlt(_localctx, 1);
      {
        setState(136);
        match(UnaryOperator);
        setState(137);
        expression();
      }
    }
    catch (RecognitionException re)
    {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    }
    finally
    {
      exitRule();
    }
    return _localctx;
  }

  public static class BinaryExpressionContext extends ParserRuleContext
  {
    public TerminalNode BinaryOperator()
    {
      return getToken(SmtParser.BinaryOperator, 0);
    }

    public List<ExpressionContext> expression()
    {
      return getRuleContexts(ExpressionContext.class);
    }

    public ExpressionContext expression(int i)
    {
      return getRuleContext(ExpressionContext.class, i);
    }

    public BinaryExpressionContext(ParserRuleContext parent, int invokingState)
    {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex()
    {
      return RULE_binaryExpression;
    }

    @Override
    public void enterRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).enterBinaryExpression(this);
      }
    }

    @Override
    public void exitRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).exitBinaryExpression(this);
      }
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor)
    {
      if (visitor instanceof SmtVisitor)
      {
        return ((SmtVisitor<? extends T>) visitor).visitBinaryExpression(this);
      }
      else
      {
        return visitor.visitChildren(this);
      }
    }
  }

  public final BinaryExpressionContext binaryExpression() throws RecognitionException
  {
    BinaryExpressionContext _localctx = new BinaryExpressionContext(_ctx, getState());
    enterRule(_localctx, 26, RULE_binaryExpression);
    try
    {
      enterOuterAlt(_localctx, 1);
      {
        setState(139);
        match(BinaryOperator);
        setState(140);
        expression();
        setState(141);
        expression();
      }
    }
    catch (RecognitionException re)
    {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    }
    finally
    {
      exitRule();
    }
    return _localctx;
  }

  public static class TernaryExpressionContext extends ParserRuleContext
  {
    public TerminalNode TernaryOperator()
    {
      return getToken(SmtParser.TernaryOperator, 0);
    }

    public List<ExpressionContext> expression()
    {
      return getRuleContexts(ExpressionContext.class);
    }

    public ExpressionContext expression(int i)
    {
      return getRuleContext(ExpressionContext.class, i);
    }

    public TernaryExpressionContext(ParserRuleContext parent, int invokingState)
    {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex()
    {
      return RULE_ternaryExpression;
    }

    @Override
    public void enterRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).enterTernaryExpression(this);
      }
    }

    @Override
    public void exitRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).exitTernaryExpression(this);
      }
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor)
    {
      if (visitor instanceof SmtVisitor)
      {
        return ((SmtVisitor<? extends T>) visitor).visitTernaryExpression(this);
      }
      else
      {
        return visitor.visitChildren(this);
      }
    }
  }

  public final TernaryExpressionContext ternaryExpression() throws RecognitionException
  {
    TernaryExpressionContext _localctx = new TernaryExpressionContext(_ctx, getState());
    enterRule(_localctx, 28, RULE_ternaryExpression);
    try
    {
      enterOuterAlt(_localctx, 1);
      {
        setState(143);
        match(TernaryOperator);
        setState(144);
        expression();
        setState(145);
        expression();
        setState(146);
        expression();
      }
    }
    catch (RecognitionException re)
    {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    }
    finally
    {
      exitRule();
    }
    return _localctx;
  }

  public static class MultiArityExpressionContext extends ParserRuleContext
  {
    public TerminalNode MultiArityOperator()
    {
      return getToken(SmtParser.MultiArityOperator, 0);
    }

    public List<ExpressionContext> expression()
    {
      return getRuleContexts(ExpressionContext.class);
    }

    public ExpressionContext expression(int i)
    {
      return getRuleContext(ExpressionContext.class, i);
    }

    public MultiArityExpressionContext(ParserRuleContext parent, int invokingState)
    {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex()
    {
      return RULE_multiArityExpression;
    }

    @Override
    public void enterRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).enterMultiArityExpression(this);
      }
    }

    @Override
    public void exitRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).exitMultiArityExpression(this);
      }
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor)
    {
      if (visitor instanceof SmtVisitor)
      {
        return ((SmtVisitor<? extends T>) visitor).visitMultiArityExpression(this);
      }
      else
      {
        return visitor.visitChildren(this);
      }
    }
  }

  public final MultiArityExpressionContext multiArityExpression() throws RecognitionException
  {
    MultiArityExpressionContext _localctx = new MultiArityExpressionContext(_ctx, getState());
    enterRule(_localctx, 30, RULE_multiArityExpression);
    try
    {
      int _alt;
      enterOuterAlt(_localctx, 1);
      {
        setState(148);
        match(MultiArityOperator);
        setState(150);
        _errHandler.sync(this);
        _alt = 1;
        do
        {
          switch (_alt)
          {
            case 1:
            {
              {
                setState(149);
                expression();
              }
            }
            break;
            default:
              throw new NoViableAltException(this);
          }
          setState(152);
          _errHandler.sync(this);
          _alt = getInterpreter().adaptivePredict(_input, 6, _ctx);
        } while (_alt != 2 && _alt != org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER);
      }
    }
    catch (RecognitionException re)
    {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    }
    finally
    {
      exitRule();
    }
    return _localctx;
  }

  public static class QuantifiedExpressionContext extends ParserRuleContext
  {
    public TerminalNode Quantifier()
    {
      return getToken(SmtParser.Quantifier, 0);
    }

    public ExpressionContext expression()
    {
      return getRuleContext(ExpressionContext.class, 0);
    }

    public List<VariableDeclarationContext> variableDeclaration()
    {
      return getRuleContexts(VariableDeclarationContext.class);
    }

    public VariableDeclarationContext variableDeclaration(int i)
    {
      return getRuleContext(VariableDeclarationContext.class, i);
    }

    public QuantifiedExpressionContext(ParserRuleContext parent, int invokingState)
    {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex()
    {
      return RULE_quantifiedExpression;
    }

    @Override
    public void enterRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).enterQuantifiedExpression(this);
      }
    }

    @Override
    public void exitRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).exitQuantifiedExpression(this);
      }
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor)
    {
      if (visitor instanceof SmtVisitor)
      {
        return ((SmtVisitor<? extends T>) visitor).visitQuantifiedExpression(this);
      }
      else
      {
        return visitor.visitChildren(this);
      }
    }
  }

  public final QuantifiedExpressionContext quantifiedExpression() throws RecognitionException
  {
    QuantifiedExpressionContext _localctx = new QuantifiedExpressionContext(_ctx, getState());
    enterRule(_localctx, 32, RULE_quantifiedExpression);
    int _la;
    try
    {
      enterOuterAlt(_localctx, 1);
      {
        setState(154);
        match(Quantifier);
        setState(155);
        match(T__0);
        setState(157);
        _errHandler.sync(this);
        _la = _input.LA(1);
        do
        {
          {
            {
              setState(156);
              variableDeclaration();
            }
          }
          setState(159);
          _errHandler.sync(this);
          _la = _input.LA(1);
        } while (_la == T__0);
        setState(161);
        match(T__2);
        setState(162);
        match(T__0);
        setState(163);
        expression();
        setState(164);
        match(T__2);
      }
    }
    catch (RecognitionException re)
    {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    }
    finally
    {
      exitRule();
    }
    return _localctx;
  }

  public static class FunctionCallExpressionContext extends ParserRuleContext
  {
    public TerminalNode Identifier()
    {
      return getToken(SmtParser.Identifier, 0);
    }

    public List<ExpressionContext> expression()
    {
      return getRuleContexts(ExpressionContext.class);
    }

    public ExpressionContext expression(int i)
    {
      return getRuleContext(ExpressionContext.class, i);
    }

    public FunctionCallExpressionContext(ParserRuleContext parent, int invokingState)
    {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex()
    {
      return RULE_functionCallExpression;
    }

    @Override
    public void enterRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).enterFunctionCallExpression(this);
      }
    }

    @Override
    public void exitRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).exitFunctionCallExpression(this);
      }
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor)
    {
      if (visitor instanceof SmtVisitor)
      {
        return ((SmtVisitor<? extends T>) visitor).visitFunctionCallExpression(this);
      }
      else
      {
        return visitor.visitChildren(this);
      }
    }
  }

  public final FunctionCallExpressionContext functionCallExpression() throws RecognitionException
  {
    FunctionCallExpressionContext _localctx = new FunctionCallExpressionContext(_ctx, getState());
    enterRule(_localctx, 34, RULE_functionCallExpression);
    try
    {
      int _alt;
      enterOuterAlt(_localctx, 1);
      {
        setState(166);
        match(Identifier);
        setState(168);
        _errHandler.sync(this);
        _alt = 1;
        do
        {
          switch (_alt)
          {
            case 1:
            {
              {
                setState(167);
                expression();
              }
            }
            break;
            default:
              throw new NoViableAltException(this);
          }
          setState(170);
          _errHandler.sync(this);
          _alt = getInterpreter().adaptivePredict(_input, 8, _ctx);
        } while (_alt != 2 && _alt != org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER);
      }
    }
    catch (RecognitionException re)
    {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    }
    finally
    {
      exitRule();
    }
    return _localctx;
  }

  public static class VariableContext extends ParserRuleContext
  {
    public TerminalNode Identifier()
    {
      return getToken(SmtParser.Identifier, 0);
    }

    public VariableContext(ParserRuleContext parent, int invokingState)
    {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex()
    {
      return RULE_variable;
    }

    @Override
    public void enterRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).enterVariable(this);
      }
    }

    @Override
    public void exitRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).exitVariable(this);
      }
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor)
    {
      if (visitor instanceof SmtVisitor)
      {
        return ((SmtVisitor<? extends T>) visitor).visitVariable(this);
      }
      else
      {
        return visitor.visitChildren(this);
      }
    }
  }

  public final VariableContext variable() throws RecognitionException
  {
    VariableContext _localctx = new VariableContext(_ctx, getState());
    enterRule(_localctx, 36, RULE_variable);
    try
    {
      enterOuterAlt(_localctx, 1);
      {
        setState(172);
        match(Identifier);
      }
    }
    catch (RecognitionException re)
    {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    }
    finally
    {
      exitRule();
    }
    return _localctx;
  }

  public static class ConstantContext extends ParserRuleContext
  {
    public BoolConstantContext boolConstant()
    {
      return getRuleContext(BoolConstantContext.class, 0);
    }

    public IntegerConstantContext integerConstant()
    {
      return getRuleContext(IntegerConstantContext.class, 0);
    }

    public UninterpretedConstantContext uninterpretedConstant()
    {
      return getRuleContext(UninterpretedConstantContext.class, 0);
    }

    public EmptySetContext emptySet()
    {
      return getRuleContext(EmptySetContext.class, 0);
    }

    public ConstantContext(ParserRuleContext parent, int invokingState)
    {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex()
    {
      return RULE_constant;
    }

    @Override
    public void enterRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).enterConstant(this);
      }
    }

    @Override
    public void exitRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).exitConstant(this);
      }
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor)
    {
      if (visitor instanceof SmtVisitor)
      {
        return ((SmtVisitor<? extends T>) visitor).visitConstant(this);
      }
      else
      {
        return visitor.visitChildren(this);
      }
    }
  }

  public final ConstantContext constant() throws RecognitionException
  {
    ConstantContext _localctx = new ConstantContext(_ctx, getState());
    enterRule(_localctx, 38, RULE_constant);
    try
    {
      setState(178);
      _errHandler.sync(this);
      switch (_input.LA(1))
      {
        case True:
        case False:
          enterOuterAlt(_localctx, 1);
        {
          setState(174);
          boolConstant();
        }
        break;
        case T__7:
        case Integer:
          enterOuterAlt(_localctx, 2);
        {
          setState(175);
          integerConstant();
        }
        break;
        case AtomPrefix:
        case UninterpretedIntPrefix:
          enterOuterAlt(_localctx, 3);
        {
          setState(176);
          uninterpretedConstant();
        }
        break;
        case T__8:
          enterOuterAlt(_localctx, 4);
        {
          setState(177);
          emptySet();
        }
        break;
        default:
          throw new NoViableAltException(this);
      }
    }
    catch (RecognitionException re)
    {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    }
    finally
    {
      exitRule();
    }
    return _localctx;
  }

  public static class BoolConstantContext extends ParserRuleContext
  {
    public TerminalNode True()
    {
      return getToken(SmtParser.True, 0);
    }

    public TerminalNode False()
    {
      return getToken(SmtParser.False, 0);
    }

    public BoolConstantContext(ParserRuleContext parent, int invokingState)
    {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex()
    {
      return RULE_boolConstant;
    }

    @Override
    public void enterRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).enterBoolConstant(this);
      }
    }

    @Override
    public void exitRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).exitBoolConstant(this);
      }
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor)
    {
      if (visitor instanceof SmtVisitor)
      {
        return ((SmtVisitor<? extends T>) visitor).visitBoolConstant(this);
      }
      else
      {
        return visitor.visitChildren(this);
      }
    }
  }

  public final BoolConstantContext boolConstant() throws RecognitionException
  {
    BoolConstantContext _localctx = new BoolConstantContext(_ctx, getState());
    enterRule(_localctx, 40, RULE_boolConstant);
    int _la;
    try
    {
      enterOuterAlt(_localctx, 1);
      {
        setState(180);
        _la = _input.LA(1);
        if (!(_la == True || _la == False))
        {
          _errHandler.recoverInline(this);
        }
        else
        {
          if (_input.LA(1) == Token.EOF)
          {
            matchedEOF = true;
          }
          _errHandler.reportMatch(this);
          consume();
        }
      }
    }
    catch (RecognitionException re)
    {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    }
    finally
    {
      exitRule();
    }
    return _localctx;
  }

  public static class IntegerConstantContext extends ParserRuleContext
  {
    public TerminalNode Integer()
    {
      return getToken(SmtParser.Integer, 0);
    }

    public IntegerConstantContext(ParserRuleContext parent, int invokingState)
    {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex()
    {
      return RULE_integerConstant;
    }

    @Override
    public void enterRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).enterIntegerConstant(this);
      }
    }

    @Override
    public void exitRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).exitIntegerConstant(this);
      }
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor)
    {
      if (visitor instanceof SmtVisitor)
      {
        return ((SmtVisitor<? extends T>) visitor).visitIntegerConstant(this);
      }
      else
      {
        return visitor.visitChildren(this);
      }
    }
  }

  public final IntegerConstantContext integerConstant() throws RecognitionException
  {
    IntegerConstantContext _localctx = new IntegerConstantContext(_ctx, getState());
    enterRule(_localctx, 42, RULE_integerConstant);
    try
    {
      setState(185);
      _errHandler.sync(this);
      switch (_input.LA(1))
      {
        case T__7:
          enterOuterAlt(_localctx, 1);
        {
          setState(182);
          match(T__7);
          setState(183);
          match(Integer);
        }
        break;
        case Integer:
          enterOuterAlt(_localctx, 2);
        {
          setState(184);
          match(Integer);
        }
        break;
        default:
          throw new NoViableAltException(this);
      }
    }
    catch (RecognitionException re)
    {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    }
    finally
    {
      exitRule();
    }
    return _localctx;
  }

  public static class UninterpretedConstantContext extends ParserRuleContext
  {
    public TerminalNode Integer()
    {
      return getToken(SmtParser.Integer, 0);
    }

    public TerminalNode AtomPrefix()
    {
      return getToken(SmtParser.AtomPrefix, 0);
    }

    public TerminalNode UninterpretedIntPrefix()
    {
      return getToken(SmtParser.UninterpretedIntPrefix, 0);
    }

    public UninterpretedConstantContext(ParserRuleContext parent, int invokingState)
    {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex()
    {
      return RULE_uninterpretedConstant;
    }

    @Override
    public void enterRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).enterUninterpretedConstant(this);
      }
    }

    @Override
    public void exitRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).exitUninterpretedConstant(this);
      }
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor)
    {
      if (visitor instanceof SmtVisitor)
      {
        return ((SmtVisitor<? extends T>) visitor).visitUninterpretedConstant(this);
      }
      else
      {
        return visitor.visitChildren(this);
      }
    }
  }

  public final UninterpretedConstantContext uninterpretedConstant() throws RecognitionException
  {
    UninterpretedConstantContext _localctx = new UninterpretedConstantContext(_ctx, getState());
    enterRule(_localctx, 44, RULE_uninterpretedConstant);
    int _la;
    try
    {
      enterOuterAlt(_localctx, 1);
      {
        setState(187);
        _la = _input.LA(1);
        if (!(_la == AtomPrefix || _la == UninterpretedIntPrefix))
        {
          _errHandler.recoverInline(this);
        }
        else
        {
          if (_input.LA(1) == Token.EOF)
          {
            matchedEOF = true;
          }
          _errHandler.reportMatch(this);
          consume();
        }
        setState(188);
        match(Integer);
      }
    }
    catch (RecognitionException re)
    {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    }
    finally
    {
      exitRule();
    }
    return _localctx;
  }

  public static class EmptySetContext extends ParserRuleContext
  {
    public SortContext sort()
    {
      return getRuleContext(SortContext.class, 0);
    }

    public EmptySetContext(ParserRuleContext parent, int invokingState)
    {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex()
    {
      return RULE_emptySet;
    }

    @Override
    public void enterRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).enterEmptySet(this);
      }
    }

    @Override
    public void exitRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).exitEmptySet(this);
      }
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor)
    {
      if (visitor instanceof SmtVisitor)
      {
        return ((SmtVisitor<? extends T>) visitor).visitEmptySet(this);
      }
      else
      {
        return visitor.visitChildren(this);
      }
    }
  }

  public final EmptySetContext emptySet() throws RecognitionException
  {
    EmptySetContext _localctx = new EmptySetContext(_ctx, getState());
    enterRule(_localctx, 46, RULE_emptySet);
    try
    {
      enterOuterAlt(_localctx, 1);
      {
        setState(190);
        match(T__8);
        setState(191);
        match(T__9);
        setState(192);
        match(T__0);
        setState(193);
        match(T__5);
        setState(194);
        sort();
        setState(195);
        match(T__2);
      }
    }
    catch (RecognitionException re)
    {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    }
    finally
    {
      exitRule();
    }
    return _localctx;
  }

  public static class GetValueContext extends ParserRuleContext
  {
    public List<ExpressionContext> expression()
    {
      return getRuleContexts(ExpressionContext.class);
    }

    public ExpressionContext expression(int i)
    {
      return getRuleContext(ExpressionContext.class, i);
    }

    public GetValueContext(ParserRuleContext parent, int invokingState)
    {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex()
    {
      return RULE_getValue;
    }

    @Override
    public void enterRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).enterGetValue(this);
      }
    }

    @Override
    public void exitRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).exitGetValue(this);
      }
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor)
    {
      if (visitor instanceof SmtVisitor)
      {
        return ((SmtVisitor<? extends T>) visitor).visitGetValue(this);
      }
      else
      {
        return visitor.visitChildren(this);
      }
    }
  }

  public final GetValueContext getValue() throws RecognitionException
  {
    GetValueContext _localctx = new GetValueContext(_ctx, getState());
    enterRule(_localctx, 48, RULE_getValue);
    int _la;
    try
    {
      enterOuterAlt(_localctx, 1);
      {
        setState(197);
        match(T__0);
        setState(203);
        _errHandler.sync(this);
        _la = _input.LA(1);
        do
        {
          {
            {
              setState(198);
              match(T__0);
              setState(199);
              expression();
              setState(200);
              expression();
              setState(201);
              match(T__2);
            }
          }
          setState(205);
          _errHandler.sync(this);
          _la = _input.LA(1);
        } while (_la == T__0);
        setState(207);
        match(T__2);
      }
    }
    catch (RecognitionException re)
    {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    }
    finally
    {
      exitRule();
    }
    return _localctx;
  }

  public static class GetUnsatCoreContext extends ParserRuleContext
  {
    public List<TerminalNode> Identifier()
    {
      return getTokens(SmtParser.Identifier);
    }

    public TerminalNode Identifier(int i)
    {
      return getToken(SmtParser.Identifier, i);
    }

    public GetUnsatCoreContext(ParserRuleContext parent, int invokingState)
    {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex()
    {
      return RULE_getUnsatCore;
    }

    @Override
    public void enterRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).enterGetUnsatCore(this);
      }
    }

    @Override
    public void exitRule(ParseTreeListener listener)
    {
      if (listener instanceof SmtListener)
      {
        ((SmtListener) listener).exitGetUnsatCore(this);
      }
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor)
    {
      if (visitor instanceof SmtVisitor)
      {
        return ((SmtVisitor<? extends T>) visitor).visitGetUnsatCore(this);
      }
      else
      {
        return visitor.visitChildren(this);
      }
    }
  }

  public final GetUnsatCoreContext getUnsatCore() throws RecognitionException
  {
    GetUnsatCoreContext _localctx = new GetUnsatCoreContext(_ctx, getState());
    enterRule(_localctx, 50, RULE_getUnsatCore);
    int _la;
    try
    {
      enterOuterAlt(_localctx, 1);
      {
        setState(209);
        match(T__0);
        setState(213);
        _errHandler.sync(this);
        _la = _input.LA(1);
        while (_la == Identifier)
        {
          {
            {
              setState(210);
              match(Identifier);
            }
          }
          setState(215);
          _errHandler.sync(this);
          _la = _input.LA(1);
        }
        setState(216);
        match(T__2);
      }
    }
    catch (RecognitionException re)
    {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    }
    finally
    {
      exitRule();
    }
    return _localctx;
  }

  public static final String _serializedATN =
      "\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3\33\u00dd\4\2\t\2" +
          "\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13" +
          "\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22\t\22" +
          "\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31\t\31" +
          "\4\32\t\32\4\33\t\33\3\2\3\2\3\2\7\2:\n\2\f\2\16\2=\13\2\3\2\7\2@\n\2" +
          "\f\2\16\2C\13\2\3\2\3\2\3\3\3\3\3\3\3\3\3\3\3\3\3\4\3\4\3\4\3\4\3\4\7" +
          "\4R\n\4\f\4\16\4U\13\4\3\4\3\4\3\4\3\4\3\4\3\5\3\5\3\5\3\5\3\5\3\6\3\6" +
          "\3\6\3\6\3\6\3\6\3\6\3\6\3\6\5\6j\n\6\3\7\3\7\3\7\3\b\3\b\6\bq\n\b\r\b" +
          "\16\br\3\t\3\t\3\n\3\n\3\13\3\13\3\f\3\f\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3" +
          "\r\3\r\3\r\3\r\3\r\5\r\u0089\n\r\3\16\3\16\3\16\3\17\3\17\3\17\3\17\3" +
          "\20\3\20\3\20\3\20\3\20\3\21\3\21\6\21\u0099\n\21\r\21\16\21\u009a\3\22" +
          "\3\22\3\22\6\22\u00a0\n\22\r\22\16\22\u00a1\3\22\3\22\3\22\3\22\3\22\3" +
          "\23\3\23\6\23\u00ab\n\23\r\23\16\23\u00ac\3\24\3\24\3\25\3\25\3\25\3\25" +
          "\5\25\u00b5\n\25\3\26\3\26\3\27\3\27\3\27\5\27\u00bc\n\27\3\30\3\30\3" +
          "\30\3\31\3\31\3\31\3\31\3\31\3\31\3\31\3\32\3\32\3\32\3\32\3\32\3\32\6" +
          "\32\u00ce\n\32\r\32\16\32\u00cf\3\32\3\32\3\33\3\33\7\33\u00d6\n\33\f" +
          "\33\16\33\u00d9\13\33\3\33\3\33\3\33\2\2\34\2\4\6\b\n\f\16\20\22\24\26" +
          "\30\32\34\36 \"$&(*,.\60\62\64\2\4\3\2\r\16\3\2\24\25\2\u00d9\2\66\3\2" +
          "\2\2\4F\3\2\2\2\6L\3\2\2\2\b[\3\2\2\2\ni\3\2\2\2\fk\3\2\2\2\16n\3\2\2" +
          "\2\20t\3\2\2\2\22v\3\2\2\2\24x\3\2\2\2\26z\3\2\2\2\30\u0088\3\2\2\2\32" +
          "\u008a\3\2\2\2\34\u008d\3\2\2\2\36\u0091\3\2\2\2 \u0096\3\2\2\2\"\u009c" +
          "\3\2\2\2$\u00a8\3\2\2\2&\u00ae\3\2\2\2(\u00b4\3\2\2\2*\u00b6\3\2\2\2," +
          "\u00bb\3\2\2\2.\u00bd\3\2\2\2\60\u00c0\3\2\2\2\62\u00c7\3\2\2\2\64\u00d3" +
          "\3\2\2\2\66\67\7\3\2\2\67;\7\4\2\28:\5\4\3\298\3\2\2\2:=\3\2\2\2;9\3\2" +
          "\2\2;<\3\2\2\2<A\3\2\2\2=;\3\2\2\2>@\5\6\4\2?>\3\2\2\2@C\3\2\2\2A?\3\2" +
          "\2\2AB\3\2\2\2BD\3\2\2\2CA\3\2\2\2DE\7\5\2\2E\3\3\2\2\2FG\7\3\2\2GH\7" +
          "\6\2\2HI\5\20\t\2IJ\5\22\n\2JK\7\5\2\2K\5\3\2\2\2LM\7\3\2\2MN\7\7\2\2" +
          "NO\5\24\13\2OS\7\3\2\2PR\5\b\5\2QP\3\2\2\2RU\3\2\2\2SQ\3\2\2\2ST\3\2\2" +
          "\2TV\3\2\2\2US\3\2\2\2VW\7\5\2\2WX\5\n\6\2XY\5\30\r\2YZ\7\5\2\2Z\7\3\2" +
          "\2\2[\\\7\3\2\2\\]\5\26\f\2]^\5\n\6\2^_\7\5\2\2_\t\3\2\2\2`j\5\20\t\2" +
          "ab\7\3\2\2bc\5\16\b\2cd\7\5\2\2dj\3\2\2\2ef\7\3\2\2fg\5\f\7\2gh\7\5\2" +
          "\2hj\3\2\2\2i`\3\2\2\2ia\3\2\2\2ie\3\2\2\2j\13\3\2\2\2kl\7\b\2\2lm\5\n" +
          "\6\2m\r\3\2\2\2np\7\t\2\2oq\5\n\6\2po\3\2\2\2qr\3\2\2\2rp\3\2\2\2rs\3" +
          "\2\2\2s\17\3\2\2\2tu\7\26\2\2u\21\3\2\2\2vw\7\30\2\2w\23\3\2\2\2xy\7\26" +
          "\2\2y\25\3\2\2\2z{\7\26\2\2{\27\3\2\2\2|\u0089\5(\25\2}\u0089\5&\24\2" +
          "~\u0089\5\32\16\2\177\u0089\5\34\17\2\u0080\u0089\5\36\20\2\u0081\u0089" +
          "\5 \21\2\u0082\u0089\5\"\22\2\u0083\u0089\5$\23\2\u0084\u0085\7\3\2\2" +
          "\u0085\u0086\5\30\r\2\u0086\u0087\7\5\2\2\u0087\u0089\3\2\2\2\u0088|\3" +
          "\2\2\2\u0088}\3\2\2\2\u0088~\3\2\2\2\u0088\177\3\2\2\2\u0088\u0080\3\2" +
          "\2\2\u0088\u0081\3\2\2\2\u0088\u0082\3\2\2\2\u0088\u0083\3\2\2\2\u0088" +
          "\u0084\3\2\2\2\u0089\31\3\2\2\2\u008a\u008b\7\20\2\2\u008b\u008c\5\30" +
          "\r\2\u008c\33\3\2\2\2\u008d\u008e\7\21\2\2\u008e\u008f\5\30\r\2\u008f" +
          "\u0090\5\30\r\2\u0090\35\3\2\2\2\u0091\u0092\7\22\2\2\u0092\u0093\5\30" +
          "\r\2\u0093\u0094\5\30\r\2\u0094\u0095\5\30\r\2\u0095\37\3\2\2\2\u0096" +
          "\u0098\7\23\2\2\u0097\u0099\5\30\r\2\u0098\u0097\3\2\2\2\u0099\u009a\3" +
          "\2\2\2\u009a\u0098\3\2\2\2\u009a\u009b\3\2\2\2\u009b!\3\2\2\2\u009c\u009d" +
          "\7\17\2\2\u009d\u009f\7\3\2\2\u009e\u00a0\5\b\5\2\u009f\u009e\3\2\2\2" +
          "\u00a0\u00a1\3\2\2\2\u00a1\u009f\3\2\2\2\u00a1\u00a2\3\2\2\2\u00a2\u00a3" +
          "\3\2\2\2\u00a3\u00a4\7\5\2\2\u00a4\u00a5\7\3\2\2\u00a5\u00a6\5\30\r\2" +
          "\u00a6\u00a7\7\5\2\2\u00a7#\3\2\2\2\u00a8\u00aa\7\26\2\2\u00a9\u00ab\5" +
          "\30\r\2\u00aa\u00a9\3\2\2\2\u00ab\u00ac\3\2\2\2\u00ac\u00aa\3\2\2\2\u00ac" +
          "\u00ad\3\2\2\2\u00ad%\3\2\2\2\u00ae\u00af\7\26\2\2\u00af\'\3\2\2\2\u00b0" +
          "\u00b5\5*\26\2\u00b1\u00b5\5,\27\2\u00b2\u00b5\5.\30\2\u00b3\u00b5\5\60" +
          "\31\2\u00b4\u00b0\3\2\2\2\u00b4\u00b1\3\2\2\2\u00b4\u00b2\3\2\2\2\u00b4" +
          "\u00b3\3\2\2\2\u00b5)\3\2\2\2\u00b6\u00b7\t\2\2\2\u00b7+\3\2\2\2\u00b8" +
          "\u00b9\7\n\2\2\u00b9\u00bc\7\30\2\2\u00ba\u00bc\7\30\2\2\u00bb\u00b8\3" +
          "\2\2\2\u00bb\u00ba\3\2\2\2\u00bc-\3\2\2\2\u00bd\u00be\t\3\2\2\u00be\u00bf" +
          "\7\30\2\2\u00bf/\3\2\2\2\u00c0\u00c1\7\13\2\2\u00c1\u00c2\7\f\2\2\u00c2" +
          "\u00c3\7\3\2\2\u00c3\u00c4\7\b\2\2\u00c4\u00c5\5\n\6\2\u00c5\u00c6\7\5" +
          "\2\2\u00c6\61\3\2\2\2\u00c7\u00cd\7\3\2\2\u00c8\u00c9\7\3\2\2\u00c9\u00ca" +
          "\5\30\r\2\u00ca\u00cb\5\30\r\2\u00cb\u00cc\7\5\2\2\u00cc\u00ce\3\2\2\2" +
          "\u00cd\u00c8\3\2\2\2\u00ce\u00cf\3\2\2\2\u00cf\u00cd\3\2\2\2\u00cf\u00d0" +
          "\3\2\2\2\u00d0\u00d1\3\2\2\2\u00d1\u00d2\7\5\2\2\u00d2\63\3\2\2\2\u00d3" +
          "\u00d7\7\3\2\2\u00d4\u00d6\7\26\2\2\u00d5\u00d4\3\2\2\2\u00d6\u00d9\3" +
          "\2\2\2\u00d7\u00d5\3\2\2\2\u00d7\u00d8\3\2\2\2\u00d8\u00da\3\2\2\2\u00d9" +
          "\u00d7\3\2\2\2\u00da\u00db\7\5\2\2\u00db\65\3\2\2\2\17;ASir\u0088\u009a" +
          "\u00a1\u00ac\u00b4\u00bb\u00cf\u00d7";
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