package edu.uiowa.smt;

import edu.uiowa.smt.parser.SmtModelVisitor;
import edu.uiowa.smt.parser.antlr.SmtLexer;
import edu.uiowa.smt.parser.antlr.SmtParser;
import edu.uiowa.smt.smtAst.SmtModel;
import edu.uiowa.smt.smtAst.SmtUnsatCore;
import edu.uiowa.smt.smtAst.SmtValues;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

public class Result
{
  public String smtProgram;
  public String satResult;
  public String model;
  public SmtModel smtModel;
  private SmtModelVisitor visitor;

  public Result()
  {
  }

  public Result(String smtProgram, String satResult)
  {
    this.smtProgram = smtProgram;
    this.satResult = satResult;
  }

  public SmtModel parseModel(String model)
  {
    SmtParser parser = getSmtParser(model);

    ParseTree tree = parser.model();
    visitor = new SmtModelVisitor();

    SmtModel smtModel = (SmtModel) visitor.visit(tree);

    return smtModel;
  }

  public SmtValues parseValues(String values)
  {
    if (this.visitor == null)
    {
      throw new RuntimeException("Result.parseValues method should only be called after Result.parseModel is called");
    }
    SmtParser parser = getSmtParser(values);
    ParseTree tree = parser.getValue();
    SmtValues smtValues = (SmtValues) this.visitor.visit(tree);
    return smtValues;
  }

  public SmtUnsatCore parseUnsatCore(String core)
  {
    SmtParser parser = getSmtParser(core);
    ParseTree tree = parser.getUnsatCore();
    SmtModelVisitor visitor = new SmtModelVisitor();
    SmtUnsatCore smtUnsatCore = (SmtUnsatCore) visitor.visit(tree);
    return smtUnsatCore;
  }

  private SmtParser getSmtParser(String values)
  {
    CharStream charStream = CharStreams.fromString(values);
    SmtLexer lexer = new SmtLexer(charStream);
    CommonTokenStream tokenStream = new CommonTokenStream(lexer);
    return new SmtParser(tokenStream);
  }
}
