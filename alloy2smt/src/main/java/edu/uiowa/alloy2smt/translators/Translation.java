package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Expr;
import edu.uiowa.alloy2smt.mapping.Mapper;
import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.printers.SmtLibPrettyPrinter;
import edu.uiowa.smt.smtAst.*;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.function.Predicate;
import java.util.stream.Collectors;

public class Translation
{

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
     * @return the satResult of translating the alloy model
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
     * @param includeScope whether to include scope in translation
     * @return the satResult of translating the given command (ignoring
     * scope constraints) into smt
     */
    public String translateCommand(int commandIndex, boolean includeScope)
    {

        Alloy2SmtTranslator commandTranslator = new Alloy2SmtTranslator(translator);

        // store old declarations and definitions
        List<Sort>                sorts                 = new ArrayList<>(commandTranslator.smtProgram.getSorts());
        List<ConstantDeclaration> constantDeclarations  = new ArrayList<>(commandTranslator.smtProgram.getConstantDeclarations());
        List<FunctionDeclaration> functionDeclarations  = new ArrayList<>(commandTranslator.smtProgram.getFunctions());


        Assertion           assertion   =  commandTranslator.translateCommand(commandIndex, includeScope);

        // get new declarations and definitions
        List<Sort> newSorts = commandTranslator.smtProgram
                .getSorts().stream()
                .filter(((Predicate<Sort>) new HashSet<>(sorts)::contains).negate())
                .collect(Collectors.toList());

        List<ConstantDeclaration> newConstantDeclarations = commandTranslator.smtProgram
                .getConstantDeclarations().stream()
                .filter(((Predicate<ConstantDeclaration>) new HashSet<>(constantDeclarations)::contains).negate())
                .collect(Collectors.toList());

        List<FunctionDeclaration> newFunctionDeclarations = commandTranslator.smtProgram
                .getFunctions().stream()
                .filter(((Predicate<FunctionDeclaration>) new HashSet<>(functionDeclarations)::contains).negate())
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

        // get the translation for the command assertion
        SmtLibPrettyPrinter printer     = new SmtLibPrettyPrinter();
        printer.visit(assertion);
        stringBuilder.append(printer.getSmtLib());
        
        return stringBuilder.toString();
    }

    /**
     * @return a translation for all commands in smt using (check-sat)
     * without getting the models
     */
    public String translateAllCommandsWithCheckSat(boolean includeScope)
    {
        StringBuilder stringBuilder = new StringBuilder(getSmtScript());
        for (int i = 0; i < translator.commands.size() ; i++)
        {
            stringBuilder.append(SmtLibPrettyPrinter.PUSH + "\n");
            stringBuilder.append(translateCommand(i, includeScope) + "\n");
            stringBuilder.append(SmtLibPrettyPrinter.CHECK_SAT + "\n");
            stringBuilder.append(SmtLibPrettyPrinter.POP + "\n");
        }
        return stringBuilder.toString();
    }

    /**
     *
     * @param expr can be Sig, Field, or Skolem
     * @return the unique id of the expr it exists in the idMap, or generate  a new id
     */
    public int getSigId(Expr expr)
    {
        return  translator.getSigId(expr);
    }
}
