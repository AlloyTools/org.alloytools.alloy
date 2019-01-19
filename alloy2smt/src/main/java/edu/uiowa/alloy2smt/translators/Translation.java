package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.Command;
import edu.uiowa.alloy2smt.mapping.Mapper;
import edu.uiowa.alloy2smt.printers.SmtLibPrettyPrinter;
import edu.uiowa.alloy2smt.smtAst.*;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.function.Predicate;
import java.util.stream.Collectors;

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
        // store old declarations and definitions
        List<Sort>                sorts                 = new ArrayList<>(translator.smtProgram.getSorts());
        List<ConstantDeclaration> constantDeclarations  = new ArrayList<>(translator.smtProgram.getConstantDeclarations());
        List<FunctionDeclaration> functionDeclarations  = new ArrayList<>(translator.smtProgram.getFunctionDeclarations());
        List<FunctionDefinition>  functionDefinitions   = new ArrayList<>(translator.smtProgram.getFunctionDefinitions());

        Assertion           assertion   =  translator.translateCommand(commandIndex);

        // get new declarations and definitions
        List<Sort> newSorts = translator.smtProgram
                .getSorts().stream()
                .filter(((Predicate<Sort>) new HashSet<>(sorts)::contains).negate())
                .collect(Collectors.toList());

        List<ConstantDeclaration> newConstantDeclarations = translator.smtProgram
                .getConstantDeclarations().stream()
                .filter(((Predicate<ConstantDeclaration>) new HashSet<>(constantDeclarations)::contains).negate())
                .collect(Collectors.toList());

        List<FunctionDeclaration> newFunctionDeclarations = translator.smtProgram
                .getFunctionDeclarations().stream()
                .filter(((Predicate<FunctionDeclaration>) new HashSet<>(functionDeclarations)::contains).negate())
                .collect(Collectors.toList());

        List<FunctionDefinition> newFunctionDefinitions = translator.smtProgram
                .getFunctionDefinitions().stream()
                .filter(((Predicate<FunctionDefinition>) new HashSet<>(functionDefinitions)::contains).negate())
                .collect(Collectors.toList());

        // get the translation for new declarations and definitions
        StringBuilder stringBuilder = new StringBuilder();
        for (Sort sort : newSorts)
        {
            SmtLibPrettyPrinter printer = new SmtLibPrettyPrinter();
            printer.visit(sort);
            stringBuilder.append(printer.getSmtLib());
        }

        for (ConstantDeclaration declaration : newConstantDeclarations)
        {
            SmtLibPrettyPrinter printer = new SmtLibPrettyPrinter();
            printer.visit(declaration);
            stringBuilder.append(printer.getSmtLib());
        }

        for (FunctionDeclaration declaration : newFunctionDeclarations)
        {
            SmtLibPrettyPrinter printer = new SmtLibPrettyPrinter();
            printer.visit(declaration);
            stringBuilder.append(printer.getSmtLib());
        }

        for (FunctionDefinition definition : newFunctionDefinitions)
        {
            SmtLibPrettyPrinter printer = new SmtLibPrettyPrinter();
            printer.visit(definition);
            stringBuilder.append(printer.getSmtLib());
        }

        // get the translation for the command assertion
        SmtLibPrettyPrinter printer     = new SmtLibPrettyPrinter();
        printer.visit(assertion);
        stringBuilder.append(printer.getSmtLib());

        //ToDo: fix repeated definitions by making smtProgram immutable
        // remove new declarations and definitions from the program

        translator.smtProgram.getSorts().removeAll(newSorts);
        translator.smtProgram.getConstantDeclarations().removeAll(newConstantDeclarations);
        translator.smtProgram.getFunctionDeclarations().removeAll(newFunctionDeclarations);
        translator.smtProgram.getFunctionDefinitions().removeAll(newFunctionDefinitions);

        return stringBuilder.toString();
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

    /**
     * @return a translation for all commands in smt using (check-sat)
     * without getting the models
     */
    public String translateAllCommandsWithCheckSat()
    {
        StringBuilder stringBuilder = new StringBuilder(getSmtScript());
        for (int i = 0; i < translator.commands.size() ; i++)
        {
            stringBuilder.append(PUSH + "\n");
            stringBuilder.append(translateCommand(i) + "\n");
            stringBuilder.append(CHECK_SAT + "\n");
            stringBuilder.append(POP + "\n");
        }
        return stringBuilder.toString();
    }
}
