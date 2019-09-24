package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.printers.SmtAstVisitor;

import java.util.*;

public class SmtSettings extends SmtAst
{
    private List<String> logic = new ArrayList<>();
    private Map<String, String> solverOptions = new HashMap<>();
    public boolean produceUnsatCore;

    public static final SmtSettings Default = new SmtSettings();

    public static final String TLIMIT = "tlimit";
    public static final String PRODUCE_UNSAT_CORES = "produce-unsat-cores";

    protected SmtSettings()
    {
        addLogic("ALL");
        putSolverOption("produce-models", "true");
        putSolverOption("incremental", "true");
        putSolverOption("finite-model-find", "true");
        putSolverOption("sets-ext", "true");
        putSolverOption("block-models", "literals");
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
