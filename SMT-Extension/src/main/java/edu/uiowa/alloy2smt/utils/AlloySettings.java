package edu.uiowa.alloy2smt.utils;

import edu.uiowa.smt.smtAst.SmtSettings;

public class AlloySettings extends SmtSettings
{
  public final static int defaultScope = 3;
  public boolean includeCommandScope;
  public static final int defaultTimeout = 30000;
  public boolean integerSingletonsOnly;
  public static AlloySettings Default = new AlloySettings();

  protected AlloySettings()
  {
    super();
    putSolverOption(TLIMIT, Integer.toString(defaultTimeout));
    includeCommandScope = false;
    integerSingletonsOnly = true;
  }

  public static AlloySettings getInstance()
  {
    return new AlloySettings(Default);
  }

  public AlloySettings(AlloySettings settings)
  {
    super(settings);
    this.includeCommandScope = settings.includeCommandScope;
    this.integerSingletonsOnly = settings.integerSingletonsOnly;
  }
}
