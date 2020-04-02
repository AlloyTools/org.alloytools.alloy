package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Expr;
import edu.uiowa.alloy2smt.mapping.Mapper;
import edu.uiowa.alloy2smt.utils.AlloySettings;
import edu.uiowa.smt.printers.SmtLibPrettyPrinter;
import edu.uiowa.smt.printers.SmtLibPrinter;
import edu.uiowa.smt.smtAst.*;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.function.Predicate;
import java.util.stream.Collectors;

public class Translation
{

    private Alloy2SmtTranslator translator;
    private final SmtScript smtAst;
    private final Mapper        mapper;
    private final String        smtScript;
    private final AlloySettings alloySettings;

    public Translation(Alloy2SmtTranslator translator, SmtScript smtAst,
                       Mapper mapper, String smtScript,
                       AlloySettings alloySettings)
    {
        this.translator = translator;
        this.smtAst     = smtAst;
        this.mapper     = mapper;
        this.smtScript  = smtScript;
        this.alloySettings = alloySettings;
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
    public SmtScript getSmtAst()
    {
        return smtAst;
    }

    public List<Command> getCommands()
    {
        return translator.commands;
    }

    /**
     * @param commandIndex the index of the command
     * @return the satResult of translating the given command (ignoring
     * scope constraints) into smt
     */
    public String translateCommand(int commandIndex)
    {

        Alloy2SmtTranslator commandTranslator = new Alloy2SmtTranslator(translator);

        // store old declarations, definitions, and assertions
        List<Sort>                sorts                 = new ArrayList<>(commandTranslator.smtScript.getSorts());
        List<ConstantDeclaration> constantDeclarations  = new ArrayList<>(commandTranslator.smtScript.getConstantDeclarations());
        List<FunctionDeclaration> functionDeclarations  = new ArrayList<>(commandTranslator.smtScript.getFunctions());
        List<Assertion> assertions = new ArrayList<>(commandTranslator.smtScript.getAssertions());


        List<Assertion> commandAssertions = commandTranslator.translateCommand(commandIndex);

        // get new declarations, definitions, and assertions
        List<Sort> newSorts = commandTranslator.smtScript
                .getSorts().stream()
                .filter(((Predicate<Sort>) new HashSet<>(sorts)::contains).negate())
                .collect(Collectors.toList());

        List<ConstantDeclaration> newConstantDeclarations = commandTranslator.smtScript
                .getConstantDeclarations().stream()
                .filter(((Predicate<ConstantDeclaration>) new HashSet<>(constantDeclarations)::contains).negate())
                .collect(Collectors.toList());

        List<FunctionDeclaration> newFunctionDeclarations = commandTranslator.smtScript
                .getFunctions().stream()
                .filter(((Predicate<FunctionDeclaration>) new HashSet<>(functionDeclarations)::contains).negate())
                .collect(Collectors.toList());

        List<Assertion> newAssertions = commandTranslator.smtScript
                .getAssertions().stream()
                .filter(((Predicate<Assertion>) new HashSet<>(assertions)::contains).negate())
                .collect(Collectors.toList());


        // get the translation for new declarations and definitions
        StringBuilder stringBuilder = new StringBuilder();
        for (Sort sort : newSorts)
        {
            SmtLibPrinter printer = new SmtLibPrettyPrinter();
            printer.visit(sort);
            stringBuilder.append(printer.getSmtLib());
        }

        for (ConstantDeclaration declaration : newConstantDeclarations)
        {
            SmtLibPrinter printer = new SmtLibPrettyPrinter();
            printer.visit(declaration);
            stringBuilder.append(printer.getSmtLib());
        }

        for (FunctionDeclaration declaration : newFunctionDeclarations)
        {
            SmtLibPrinter printer = new SmtLibPrettyPrinter();
            printer.visit(declaration);
            stringBuilder.append(printer.getSmtLib());
        }

        for (Assertion newAssertion : newAssertions)
        {
            SmtLibPrinter printer = new SmtLibPrettyPrinter();
            printer.visit(newAssertion);
            stringBuilder.append(printer.getSmtLib());
        }

        // get the translation for the command assertion
        SmtLibPrinter printer     = new SmtLibPrettyPrinter();
        for (Assertion assertion: commandAssertions)
        {
            printer.visit(assertion);
        }

        stringBuilder.append(printer.getSmtLib());
        
        return stringBuilder.toString();
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
            stringBuilder.append(SmtLibPrinter.PUSH + "\n");
            stringBuilder.append(translateCommand(i) + "\n");
            stringBuilder.append(SmtLibPrinter.CHECK_SAT + "\n");
            stringBuilder.append(SmtLibPrinter.POP + "\n");
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
