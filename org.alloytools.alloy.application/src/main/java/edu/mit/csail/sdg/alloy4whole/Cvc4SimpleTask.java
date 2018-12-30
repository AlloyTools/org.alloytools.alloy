package edu.mit.csail.sdg.alloy4whole;

import edu.mit.csail.sdg.alloy4.*;

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
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

import edu.mit.csail.sdg.alloy4whole.solution.*;

public class Cvc4SimpleTask implements WorkerEngine.WorkerTask
{
    public static final String OS                   = System.getProperty("os.name");
    public static final String SEP                  = File.separator;
    public static final String BIN_PATH             = System.getProperty("user.dir")+SEP+"bin"+SEP;
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

        workerCallback.callback(new Object[]{"S2","\n"});
        workerCallback.callback(new Object[]{"S2", "Translation time: " + (endTranslate - startTranslate) + " ms\n"});
        workerCallback.callback(new Object[]{"S2","\n"});

        String smtScript            = translation.getSmtScript();
        String command              = translation.translateCommand(0);

        smtScript += command + Translation.CHECK_SAT + "\n" + Translation.GET_MODEL;

        if(smtScript != null)
        {
            final long startSolve   = System.currentTimeMillis();
            String smtResult        = solve(smtScript, workerCallback);
            final long endSolve     = System.currentTimeMillis();
            long duration		        = (endSolve - startSolve);

            workerCallback.callback(new Object[]{"S2","\n"});
            workerCallback.callback(new Object[]{"S2","Solving time: " + duration + " ms\n"});
            workerCallback.callback(new Object[]{"S2","\n"});

            if(smtResult != null)
            {
                Scanner scanner = new Scanner(smtResult);
                String  result  = scanner.next();

                switch (result)
                {
                    case "sat":
                            prepareInstance(workerCallback, translation, duration, scanner);
                        break;
                    case "unsat":
                        workerCallback.callback(new Object[]{"S2", "No model found\n"});
                        break;
                    default:
                        workerCallback.callback(new Object[]{"S2","No result found\n"});
                        break;
                }
            }
        }
    }

    private void prepareInstance(WorkerEngine.WorkerCallback workerCallback, Translation translation, long duration, Scanner scanner) throws Exception
    {
        workerCallback.callback(new Object[]{"S2","A model has been found\n"});

        //construct A4Solution from smt result
        StringBuilder SmtModel = new StringBuilder();
        while(scanner.hasNext())
        {
            SmtModel.append(scanner.nextLine() + "\n");
        }

        edu.uiowa.alloy2smt.smtAst.SmtModel model = parseModel(SmtModel.toString());

        //ToDo: implement the case when there are multiple files

        Iterator<Map.Entry<String, String>> iterator = alloyFiles.entrySet().iterator();

        Map.Entry<String, String> entry = iterator.next();

        File xmlFile        = File.createTempFile("tmp", ".smt.xml", new File(tempDirectory));

        String xmlFilePath  = xmlFile.getAbsolutePath();

        writeModelToAlloyXmlFile(translation.getMapper(), model, xmlFilePath, entry.getKey());

        workerCallback.callback(new Object[]{"S2","\n"});
        workerCallback.callback(new Object[]{"S2","Generated alloy instance file: " + xmlFilePath +"\n"});
        workerCallback.callback(new Object[]{"S2","\n"});

        String  satResult           = "sat";
        boolean isCounterExample    = false;
        int expected                = -1;
        String solutionXMLFile      = xmlFilePath;
        String formula              = "";

        Object[] message            = new Object []{satResult, isCounterExample, expected, solutionXMLFile, formula, duration};
        workerCallback.callback(message);
    }

    private void writeModelToAlloyXmlFile(Mapper mapper, SmtModel model, String xmlFile,
                                          String alloyFileName) throws Exception
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
        instance.bitWidth = 4;
        instance.maxSeq = 4; //ToDo: review the maxSeq meaning
        instance.command = "Run Default for 4 but 4 int, 4 seq expect 0";

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

        workerCallback.callback(new Object[]{"S2","\n"});
        workerCallback.callback(new Object[]{"S2","Generated a mapping file: " + jsonFile.getAbsolutePath() +"\n"});
        workerCallback.callback(new Object[]{"S2","\n"});

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

    private String solve(String smtFormula, WorkerEngine.WorkerCallback workerCallback) throws Exception
    {
        String cvc4;

        if(OS.startsWith("Windows"))
        {
            cvc4 = BIN_PATH + "cvc4_win64.exe";
        }
        else if(OS.startsWith("Linux"))
        {
            cvc4 = BIN_PATH + "cvc4_linux";
        }
        else
        {
            throw new Exception("No CVC4 binary available for the OS: " + OS);
        }
        if(smtFormula == null)
        {
            throw new Exception("No input file for CVC4!");
        }

        File cvc4Binary = new File(cvc4);

        if(!cvc4Binary.exists())
        {
            throw new Exception("CVC4 binary does not exist at: " + cvc4);
        }
        if(!cvc4Binary.canExecute())
        {
            throw new Exception("CVC4 binary cannot be executed at: " + cvc4);
        }

        ProcessBuilder  processBuilder = new ProcessBuilder();
        List<String>    command       = new ArrayList<>();

        command.add(cvc4);

        // tell cvc4 the input language is smt2
        command.add("--lang");
        command.add("smtlib2.6");

        processBuilder.command(command);

        workerCallback.callback(new Object[]{"S2","Executing command: " + String.join(" ", command) + "\n\n"});

        Process process = processBuilder.start();

        OutputStream processInput = process.getOutputStream();

        processInput.write(smtFormula.getBytes());

        processInput.close();

        if(process.waitFor(SOLVING_TIMEOUT, TimeUnit.SECONDS))
        {
            String error = getProcessOutput(process.getErrorStream());

            if(!error.isEmpty())
            {
                throw new Exception(error);
            }

            String cvc4Output = getProcessOutput(process.getInputStream());
            workerCallback.callback(new Object[]{"S2","CVC4 Output:\n\n" + cvc4Output + "\n"});

            return cvc4Output;
        }
        else
        {
            workerCallback.callback(new Object[]{"S2","CVC4 Timeout: " + SOLVING_TIMEOUT + " seconds\n"});
            process.destroy();
            return null;
        }
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
