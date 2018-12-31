package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.Command;
import edu.uiowa.alloy2smt.mapping.Mapper;
import edu.uiowa.alloy2smt.printers.SmtLibPrettyPrinter;
import edu.uiowa.alloy2smt.smtAst.Assertion;
import edu.uiowa.alloy2smt.smtAst.SmtProgram;
import edu.uiowa.alloy2smt.smtAst.SolverOption;

import java.util.List;
import java.util.Map;

public class Translation
{
    public final static String CHECK_SAT    = "(check-sat)";
    public final static String GET_MODEL    = "(get-model)";
    public final static String PUSH         = "(push)";
    public final static String POP          = "(pop)";

    private Alloy2SmtTranslator translator;
    private final SmtProgram    smtAst;
    private final Mapper        mapper;
    private final String        smtScript;

    public Translation(Alloy2SmtTranslator translator, SmtProgram smtAst, Mapper mapper, String smtScript)
    {
        this.translator = translator;
        this.smtAst     = smtAst;
        this.mapper     = mapper;
        this.smtScript  = smtScript;
    }

    /**
     * @return the result of translating the alloy model
     * (excluding assertions and commands like check and run) into smt.
     * Command translation is handled separately  by the method
     * {@link Translation#translateCommand(int)}
     */
    public String getSmtScript()
    {
        return smtScript;
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
     * @return an abstract syntax tree for the smt translation
     */
    public SmtProgram getSmtAst()
    {
        return smtAst;
    }

    public List<Command> getCommands()
    {
        return translator.commands;
    }

    /**
     * @param commandIndex the index of the command
     * @return the result of translating the given command (ignoring
     * scope constraints) into smt
     */
    public String translateCommand(int commandIndex)
    {
        Assertion           assertion   =  translator.translateCommand(commandIndex);
        SmtLibPrettyPrinter printer     = new SmtLibPrettyPrinter();
        printer.visit(assertion);
        return printer.getSmtLib();
    }

    public String translateOptions(Map<String, String> options)
    {
        SmtLibPrettyPrinter printer = new SmtLibPrettyPrinter();

        for (Map.Entry<String, String> entry: options.entrySet())
        {
            SolverOption option = new SolverOption(entry.getKey(), entry.getValue());
            printer.visit(option);
        }
        return printer.getSmtLib();
    }
}
