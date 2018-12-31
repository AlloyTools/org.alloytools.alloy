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

import javax.swing.*;

public class Cvc4SimpleTask implements WorkerEngine.WorkerTask
{
    public static final String tempDirectory        = System.getProperty("java.io.tmpdir");
    public static final int SOLVING_TIMEOUT         = 300;
    private final Map<String, String> alloyFiles;

    Cvc4SimpleTask(Map<String, String> alloyFiles)
    {
        this.alloyFiles  = alloyFiles;
    }
    @Override
    public void run(WorkerEngine.WorkerCallback workerCallback) throws Exception
    {
        final long startTranslate   = System.currentTimeMillis();

        Translation translation     = translateToSMT(workerCallback);

        final long endTranslate     = System.currentTimeMillis();

        callback(workerCallback, "Translation time: " + (endTranslate - startTranslate) + " ms\n");

        String smtScript            = translation.getSmtScript();

        if(smtScript != null)
        {
            Cvc4Process cvc4Process     = Cvc4Process.start(workerCallback);

            cvc4Process.sendCommand(smtScript);

            for (int index = 0; index < translation.getCommands().size(); index++)
            {
                String commandTranslation = translation.translateCommand(index);

                final long startSolve   = System.currentTimeMillis();

                callback(workerCallback, "Executing " + translation.getCommands().get(index).label + "\n");

                // (push)
                // (check-sat)
                cvc4Process.sendCommand(Translation.PUSH + "\n" + commandTranslation + Translation.CHECK_SAT);

                // read the result
                String result = cvc4Process.receiveOutput();

                final long endSolve     = System.currentTimeMillis();
                long duration		    = (endSolve - startSolve);
                callback(workerCallback, "Solving time: " + duration + " ms\n");

                callback(workerCallback, "Satisfiability: " + result);

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
                                callback(workerCallback, "The assert is valid\n");
                            }
                            else
                            {
                                callback(workerCallback, "The result is unsat\n");
                            }
                            break;
                        default:
                            callback(workerCallback,"The result is unknown\n");
                            break;
                    }
                }
                else
                {
                    callback(workerCallback,"No result returned from cvc4\n");
                }

                // (pop)
                cvc4Process.sendCommand(Translation.POP);
            }

            cvc4Process.destroy();
        }
        else
        {
            callback(workerCallback, "No translation found from alloy model to SMT");
        }
    }

    private void callback(WorkerEngine.WorkerCallback workerCallback, String log)
    {
        workerCallback.callback(new Object[]{"S2", "\n"});
        workerCallback.callback(new Object[]{"S2", log});
        workerCallback.callback(new Object[]{"S2", "\n"});
    }

    private void prepareInstance(WorkerEngine.WorkerCallback workerCallback, Translation translation, int commandIndex, long duration, Cvc4Process cvc4Process) throws Exception
    {
        cvc4Process.sendCommand(Translation.GET_MODEL);

        String smtModel = cvc4Process.receiveOutput();

        callback(workerCallback,"A model has been found\n");
        callback(workerCallback, smtModel);

        Command command = translation.getCommands().get(commandIndex);
        SmtModel model = parseModel(smtModel);

        //ToDo: implement the case when there are multiple files

        Iterator<Map.Entry<String, String>> iterator = alloyFiles.entrySet().iterator();

        Map.Entry<String, String> entry = iterator.next();

        File xmlFile        = File.createTempFile("tmp", ".smt.xml", new File(tempDirectory));

        String xmlFilePath  = xmlFile.getAbsolutePath();

        writeModelToAlloyXmlFile(translation.getMapper(), model, xmlFilePath, entry.getKey(), command);

        callback(workerCallback, "Generated alloy instance file: " + xmlFilePath +"\n");

        String  satResult           = "sat";
        String solutionXMLFile      = xmlFilePath;

        Object[] message            = new Object []{satResult, command.check, command.expects, solutionXMLFile, command.toString(), duration};
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
        //ToDo: implement the case when there are multiple files

        Iterator<Map.Entry<String, String>> iterator    = alloyFiles.entrySet().iterator();

        Map.Entry<String, String> entry                 = iterator.next();

        Translation translation                         = Utils.translate(entry.getValue());

        workerCallback.callback(new Object[]{"S2","Translation output:\n\n" + translation.getSmtScript() + "\n"});

        File jsonFile = File.createTempFile("tmp", ".mapping.json", new File(tempDirectory));
        // output the mapping

        translation.getMapper().writeToJson(jsonFile.getPath());

        callback(workerCallback, "Generated a mapping file: " + jsonFile.getAbsolutePath() +"\n");

        return translation;
    }

    private String getProcessOutput(InputStream inputStream)
    {
        StringBuilder stringBuilder = new StringBuilder();

        Scanner scanner = new Scanner(inputStream);

        while(scanner.hasNextLine())
        {
            stringBuilder.append(scanner.nextLine()).append("\n");
        }

        return stringBuilder.toString();
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
