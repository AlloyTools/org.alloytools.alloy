package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Expr;
import edu.uiowa.alloy2smt.mapping.Mapper;
import edu.uiowa.alloy2smt.utils.AlloySettings;
import edu.uiowa.smt.optimizer.SmtRewriter;
import edu.uiowa.smt.printers.SmtLibPrinter;
import edu.uiowa.smt.smtAst.SmtScript;

import java.util.List;

public class Translation
{

  private Alloy2SmtTranslator translator;
  private final Mapper mapper;
  private final AlloySettings alloySettings;
  private SmtScript optimizedSmtScript;

  public Translation(Alloy2SmtTranslator translator, SmtScript smtScript,
                     Mapper mapper,
                     AlloySettings alloySettings)
  {
    this.translator = translator;
    this.mapper = mapper;
    this.alloySettings = alloySettings;
  }

  public AlloySettings getAlloySettings()
  {
    return alloySettings;
  }

  /**
   * @return a mapper that maps alloy signatures and fields into their
   * corresponding functions in the generated smt script
   */
  public Mapper getMapper()
  {
    return mapper;
  }

  /**
   * @return an abstract syntax tree for the original smt translation
   */
  public SmtScript getOriginalSmtScript()
  {
    return translator.getSmtScript();
  }

  /**
   * @return the optimized smt translation for alloy model without commands
   */
  public SmtScript getOptimizedSmtScript()
  {
    return optimizedSmtScript;
  }

  /**
   * @return the optimized smt translation for the given command
   */
  public SmtScript getOptimizedSmtScript(int index)
  {
    return optimizedSmtScript.getChild(index);
  }

  public List<Command> getCommands()
  {
    return translator.commands;
  }

  /**
   * @param isOptimized
   * @return a translation for all commands in smt using (check-sat)
   * without getting the models
   */
  public String translateAllCommandsWithCheckSat(boolean isOptimized)
  {
    StringBuilder stringBuilder = new StringBuilder();
    if (isOptimized)
    {
      stringBuilder.append(getOptimizedSmtScript().print(alloySettings));
    }
    else
    {
      stringBuilder.append(getOriginalSmtScript().print(alloySettings));
    }
    for (int i = 0; i < translator.commands.size(); i++)
    {
      stringBuilder.append(SmtLibPrinter.PUSH + "\n");
      if (isOptimized)
      {
        stringBuilder.append(getOptimizedSmtScript(i) + "\n");
      }
      else
      {
        stringBuilder.append(getOriginalSmtScript(i) + "\n");
      }
      stringBuilder.append(SmtLibPrinter.CHECK_SAT + "\n");
      stringBuilder.append(SmtLibPrinter.POP + "\n");
    }
    return stringBuilder.toString();
  }

  private SmtScript getOriginalSmtScript(int index)
  {
    return translator.smtScript.getChild(index);
  }

  /**
   * @param expr can be Sig, Field, or Skolem
   * @return the unique id of the expr it exists in the idMap, or generate  a new id
   */
  public int getSigId(Expr expr)
  {
    return translator.getSigId(expr);
  }

  public void optimize()
  {
    SmtRewriter smtRewriter = new SmtRewriter();
    this.optimizedSmtScript = (SmtScript) smtRewriter.visit(translator.smtScript).smtAst;
  }
}
