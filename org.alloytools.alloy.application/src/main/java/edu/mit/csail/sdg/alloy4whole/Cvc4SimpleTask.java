package edu.mit.csail.sdg.alloy4whole;

import edu.mit.csail.sdg.alloy4.*;

import edu.mit.csail.sdg.ast.Command;
import edu.uiowa.alloy2smt.Utils;
import edu.uiowa.alloy2smt.mapping.Mapper;
import edu.uiowa.alloy2smt.mapping.MappingField;
import edu.uiowa.alloy2smt.mapping.MappingSignature;
import edu.uiowa.alloy2smt.smtAst.*;
import edu.uiowa.alloy2smt.smtparser.SmtModelVisitor;
import edu.uiowa.alloy2smt.smtparser.antlr.SmtLexer;
import edu.uiowa.alloy2smt.smtparser.antlr.SmtParser;
import edu.uiowa.alloy2smt.translators.Translation;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

import java.io.*;
import java.util.*;
import java.util.stream.Collectors;

import edu.mit.csail.sdg.alloy4whole.solution.*;

import static edu.mit.csail.sdg.alloy4.A4Preferences.Cvc4Timeout;

public class Cvc4SimpleTask implements WorkerEngine.WorkerTask
{
    private static final String tempDirectory        = System.getProperty("java.io.tmpdir");
    private static final String TIMEOUT_OPTION       = "tlimit" ;

    private final Map<String, String> alloyFiles;
    private final String              originalFileName;
    private final int                 resolutionMode;

    Cvc4SimpleTask(Map<String, String> alloyFiles, String originalFilename, int resolutionMode)
    {
        this.alloyFiles         = alloyFiles;
        this.originalFileName   = originalFilename;
        this.resolutionMode     = resolutionMode;
    }
    @Override
    public void run(WorkerEngine.WorkerCallback workerCallback) throws Exception
    {
        try
        {
            final long startTranslate = System.currentTimeMillis();

            Translation translation = translateToSMT(workerCallback);

            final long endTranslate = System.currentTimeMillis();

            callbackBold(workerCallback, "Translation time: " + (endTranslate - startTranslate) + " ms\n");

            String smtScript = translation.getSmtScript();

            if (smtScript != null) {
                Cvc4Process cvc4Process = Cvc4Process.start(workerCallback);

                cvc4Process.sendCommand(smtScript);

                setSolverOptions(translation, cvc4Process, workerCallback);

                for (int index = 0; index < translation.getCommands().size(); index++) {
                    solveCommand(translation, index, cvc4Process, workerCallback);
                }

                cvc4Process.destroy();
            } else {
                callbackPlain(workerCallback, "No translation found from alloy model to SMT");
            }
        }
        catch (Exception exception)
        {
            StringWriter stringWriter = new StringWriter();
            exception.printStackTrace(new PrintWriter(stringWriter));
            throw new Exception(stringWriter.toString());
        }
    }

    private void setSolverOptions(Translation translation, Cvc4Process cvc4Process, WorkerEngine.WorkerCallback workerCallback) throws IOException
    {
        Map<String, String> options = new HashMap<>();

        // (set-option :tlimit 30000)
        options.put(TIMEOUT_OPTION, Cvc4Timeout.get().toString());

        String script = translation.translateOptions(options);
        cvc4Process.sendCommand(script);
        callbackPlain(workerCallback, script);
    }

    private void solveCommand(Translation translation, int index, Cvc4Process cvc4Process, WorkerEngine.WorkerCallback workerCallback) throws Exception
    {
        String commandTranslation = translation.translateCommand(index);

        final long startSolve   = System.currentTimeMillis();

        callbackBold(workerCallback, "Executing " + translation.getCommands().get(index).label + "\n");

        // (push)
        // (check-sat)
        callbackPlain(workerCallback, Translation.PUSH + "\n" + commandTranslation + Translation.CHECK_SAT);
        String result = cvc4Process.sendCommand(Translation.PUSH + "\n" + commandTranslation + Translation.CHECK_SAT);

        final long endSolve     = System.currentTimeMillis();
        long duration		    = (endSolve - startSolve);
        callbackBold(workerCallback, "Solving time: " + duration + " ms\n");

        callbackBold(workerCallback, "Satisfiability: " + result + "\n");

        if(result != null)
        {
            switch (result)
            {
                case "sat":
                    prepareInstance(workerCallback, translation, index, duration, cvc4Process);
                    break;
                case "unsat":
                    if(translation.getCommands().get(index).check)
                    {
                        callbackPlain(workerCallback, "The assertion is valid\n");
                    }
                    else
                    {
                        callbackPlain(workerCallback, "The result is unsat\n");
                    }
                    break;
                default:
                    callbackPlain(workerCallback,"The result is unknown\n");
                    break;
            }
        }
        else
        {
            callbackPlain(workerCallback,"No result returned from cvc4\n");
        }

        // (pop)
        cvc4Process.sendCommand(Translation.POP);
        callbackPlain(workerCallback, Translation.POP + "\n");
    }

    private void callbackPlain(WorkerEngine.WorkerCallback workerCallback, String log)
    {
        workerCallback.callback(new Object[]{"", log});
        workerCallback.callback(new Object[]{"", ""});
    }

    private void callbackBold(WorkerEngine.WorkerCallback workerCallback, String log)
    {
        workerCallback.callback(new Object[]{"S2", "\n"});
        workerCallback.callback(new Object[]{"S2", log});
        workerCallback.callback(new Object[]{"S2", "\n"});
    }

    private void prepareInstance(WorkerEngine.WorkerCallback workerCallback, Translation translation, int commandIndex, long duration, Cvc4Process cvc4Process) throws Exception
    {
        String smtModel = cvc4Process.sendCommand(Translation.GET_MODEL);

        callbackPlain(workerCallback,"A model has been found\n");
        callbackPlain(workerCallback, smtModel);

        Command command = translation.getCommands().get(commandIndex);
        SmtModel model = parseModel(smtModel);

        File xmlFile        = File.createTempFile("tmp", ".smt.xml", new File(tempDirectory));

        String xmlFilePath  = xmlFile.getAbsolutePath();

        writeModelToAlloyXmlFile(translation.getMapper(), model, xmlFilePath, originalFileName, command);

        callbackPlain(workerCallback, "Generated alloy instance file: " + xmlFilePath +"\n");

        String  satResult           = "sat";

        Object[] message            = new Object []{satResult, command.check, command.expects, xmlFilePath, command.toString(), duration};
        workerCallback.callback(message);
    }

    private void writeModelToAlloyXmlFile(Mapper mapper, SmtModel model, String xmlFile,
                                          String alloyFileName, Command command) throws Exception
    {

        Map<String, FunctionDefinition> functionsMap = new HashMap<>();

        for(FunctionDefinition function: model.getFunctionDefinitions())
        {
            functionsMap.put(function.funcName, function);
        }

        List<Signature> signatures = new ArrayList<>();

        for (MappingSignature mappingSignature : mapper.signatures )
        {
            Signature signature = getSignature(functionsMap, mappingSignature);
            signatures.add(signature);
        }

        List<Field> fields = new ArrayList<>();

        for (MappingField mappingField : mapper.fields )
        {
            Field field = getField(functionsMap, mappingField);
            fields.add(field);
        }

        Instance instance   = new Instance();
        instance.signatures = signatures;
        instance.fields     = fields;
        instance.bitWidth   = 4;
        instance.maxSeq     = 4; //ToDo: review the maxSeq meaning
        instance.command    = command.toString();

        instance.fileName = alloyFileName;

        Alloy alloy = new Alloy();
        alloy.instances = new ArrayList<>();
        alloy.instances.add(instance);

        alloy.writeToXml(xmlFile);
    }

    private Signature getSignature(Map<String, FunctionDefinition> functionsMap, MappingSignature mappingSignature) throws Exception
    {
        Signature signature  = new Signature();

        // get signature info from the mapping
        signature.label         = mappingSignature.label;
        signature.id            = mappingSignature.id;
        signature.parentId  	= mappingSignature.parentId;

        signature.builtIn       = mappingSignature.builtIn ? "yes" : "no";
        signature.isAbstract    = mappingSignature.isAbstract? "yes" : "no";
        signature.isOne         = mappingSignature.isOne? "yes" : "no";
        signature.isLone        = mappingSignature.isLone? "yes" : "no";
        signature.isSome        = mappingSignature.isSome? "yes" : "no";
        signature.isPrivate     = mappingSignature.isPrivate? "yes" : "no";
        signature.isMeta        = mappingSignature.isMeta? "yes" : "no";
        signature.isExact   	= mappingSignature.isExact ? "yes" : "no";
        signature.isEnum        = mappingSignature.isEnum? "yes" : "no";

        // get the corresponding function from the model
        FunctionDefinition function = functionsMap.get(mappingSignature.functionName);
        if(function == null)
        {
            throw new Exception("Can not find the function "+ mappingSignature.functionName
                    + " for signature "+ signature.label + "in the model.") ;
        }

        signature.atoms = getAtoms(function.expression);
        return signature;
    }

    private Field getField(Map<String,FunctionDefinition> functionsMap, MappingField mappingField) throws Exception
    {
        Field field  = new Field();

        // get field info from the mapping
        field.label         = mappingField.label;
        field.id            = mappingField.id;
        field.parentId  	= mappingField.parentId;

        field.isPrivate     = mappingField.isPrivate? "yes" : "no";
        field.isMeta        = mappingField.isMeta? "yes" : "no";

        // get the corresponding function from the model
        FunctionDefinition function = functionsMap.get(mappingField.functionName);
        if(function == null)
        {
            throw new Exception("Can not find the function "+ mappingField.functionName
                    + " for field "+ field.label + "in the model.") ;
        }

        field.tuples = getTuples(function.expression);
        field.types  = getTypes(mappingField);

        return field;
    }

    private Types getTypes(MappingField mappingField)
    {
        Types types = new Types();

        types.types = mappingField.types.stream()
                .map(t -> new Type(t.id)).collect(Collectors.toList());
        return types;
    }

    private List<Tuple> getTuples(Expression expression)
    {
        List<Tuple> tuples = new ArrayList<>();

        if(expression instanceof  UnaryExpression)
        {
            UnaryExpression unary = (UnaryExpression) expression;
            switch (unary.getOP())
            {
                case EMPTYSET: return new ArrayList<>();
                case SINGLETON:
                {
                    Expression unaryExpression = unary.getExpression();
                    if(unaryExpression instanceof MultiArityExpression)
                    {
                        MultiArityExpression multiArity = (MultiArityExpression) unaryExpression;

                        if(multiArity.getOp() == MultiArityExpression.Op.MKTUPLE)
                        {
                            List<Atom> atoms    = getAtoms(multiArity);
                            Tuple tuple         = new Tuple();
                            tuple.atoms         = atoms;
                            return Collections.singletonList(tuple);
                        }

                        throw new UnsupportedOperationException();
                    }
                    throw new UnsupportedOperationException();
                }
                default:
                    throw new UnsupportedOperationException();
            }
        }

        if(expression instanceof  BinaryExpression)
        {
            BinaryExpression binary = (BinaryExpression) expression;

            switch (binary.getOp())
            {
                case UNION:
                {
                    tuples.addAll(getTuples(binary.getLhsExpr()));
                    tuples.addAll(getTuples(binary.getRhsExpr()));
                    return tuples;
                }
                default:
                    throw new UnsupportedOperationException();
            }
        }

        throw new UnsupportedOperationException();
    }

    private List<Atom> getAtoms(Expression expression)
    {
        List<Atom> atoms = new ArrayList<>();


        if(expression instanceof  AtomConstant)
        {
            AtomConstant atomConstant = (AtomConstant) expression;
            atoms.add(new Atom(atomConstant.getName()));
            return  atoms;
        }

        if(expression instanceof  UnaryExpression)
        {
            UnaryExpression unary = (UnaryExpression) expression;
            switch (unary.getOP())
            {
                case EMPTYSET: return new ArrayList<>();
                case SINGLETON:
                    {
                        return getAtoms(unary.getExpression());
                    }
                default:
                    throw new UnsupportedOperationException();
            }
        }

        if(expression instanceof  BinaryExpression)
        {
            BinaryExpression binary = (BinaryExpression) expression;

            switch (binary.getOp())
            {
                case UNION:
                {
                    atoms.addAll(getAtoms(binary.getLhsExpr()));
                    atoms.addAll(getAtoms(binary.getRhsExpr()));
                    return atoms;
                }
                default:
                    throw new UnsupportedOperationException();
            }
        }

        if(expression instanceof MultiArityExpression)
        {
            MultiArityExpression multiArity = (MultiArityExpression) expression;
            switch (multiArity.getOp())
            {
                case MKTUPLE:
                {
                    for (Expression expr: multiArity.getExpressions())
                    {
                        atoms.addAll(getAtoms(expr));
                    }

                    return atoms;
                }

                default:
                    throw new UnsupportedOperationException();
            }
        }

        throw new UnsupportedOperationException();
    }

    private Translation translateToSMT(WorkerEngine.WorkerCallback workerCallback) throws IOException
    {
        Translation translation = Utils.translate(alloyFiles, originalFileName, resolutionMode);

        callbackBold(workerCallback,"Translation output");
        callbackPlain(workerCallback, translation.getSmtScript());

        File jsonFile = File.createTempFile("tmp", ".mapping.json", new File(tempDirectory));
        // output the mapping

        translation.getMapper().writeToJson(jsonFile.getPath());

        callbackPlain(workerCallback, "Generated a mapping file: " + jsonFile.getAbsolutePath() +"\n");

        return translation;
    }

    private SmtModel parseModel(String model)
    {
        CharStream charStream = CharStreams.fromString(model);

        SmtLexer lexer = new SmtLexer(charStream);
        CommonTokenStream tokenStream = new CommonTokenStream(lexer);
        SmtParser parser = new SmtParser(tokenStream);

        ParseTree tree =  parser.model();
        SmtModelVisitor visitor = new SmtModelVisitor();

        SmtModel smtModel = (SmtModel) visitor.visit(tree);

        return  smtModel;
    }
}
