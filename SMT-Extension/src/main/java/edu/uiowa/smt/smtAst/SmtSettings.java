package edu.uiowa.smt.smtAst;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class SmtSettings extends SmtAst
{
  private List<String> logic = new ArrayList<>();
  private Map<String, String> solverOptions = new HashMap<>();
  public boolean produceUnsatCore;
  public boolean finiteModelFinding;

  public static final SmtSettings Default = new SmtSettings();

  public static final String TLIMIT = "tlimit";
  public static final String PRODUCE_UNSAT_CORES = "produce-unsat-cores";
  public static final String FINITE_MODEL_FIND = "finite-model-find";

  protected SmtSettings()
  {
    addLogic("ALL");
    putSolverOption("produce-models", "true");
    putSolverOption("incremental", "true");
    putSolverOption("sets-ext", "true");
    putSolverOption("block-models", "literals");
    putSolverOption(FINITE_MODEL_FIND, Boolean.toString(true));
    putSolverOption("cegqi-all", "false");
    finiteModelFinding = true;
    produceUnsatCore = false;
  }

  public static SmtSettings getInstance()
  {
    return new SmtSettings(Default);
  }

  public SmtSettings(SmtSettings settings)
  {
    logic = new ArrayList<>(settings.logic);
    solverOptions = new HashMap<>(settings.solverOptions);
    produceUnsatCore = settings.produceUnsatCore;
    finiteModelFinding = settings.finiteModelFinding;
  }

  public void addLogic(String logic)
  {
    this.logic.add(logic);
  }

  public List<String> getLogic()
  {
    return logic;
  }

  public Map<String, String> getSolverOptions()
  {
    return solverOptions;
  }

  public void putSolverOption(String key, String value)
  {
    solverOptions.put(key, value);
  }


  @Override
  public void accept(SmtAstVisitor visitor)
  {
    visitor.visit(this);
  }
}
