package edu.mit.csail.sdg.alloy4whole;

import edu.mit.csail.sdg.alloy4.*;

import edu.uiowa.alloy2smt.Utils;
import edu.uiowa.alloy2smt.smtAst.SmtModel;
import edu.uiowa.alloy2smt.smtparser.SmtModelVisitor;
import edu.uiowa.alloy2smt.smtparser.antlr.SmtLexer;
import edu.uiowa.alloy2smt.smtparser.antlr.SmtParser;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Marshaller;
import java.io.*;
import java.util.*;
import java.util.concurrent.TimeUnit;

import edu.mit.csail.sdg.alloy4whole.solution.*;

public class Cvc4SimpleTask implements WorkerEngine.WorkerTask
{
    public static final String OS                   = System.getProperty("os.name");
    public static final String SEP                  = File.separator;
    public static final String BIN_PATH             = System.getProperty("user.dir")+SEP+"bin"+SEP;
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

        String smtFormula          = translateToSMT(workerCallback);

        final long endTranslate     = System.currentTimeMillis();

        workerCallback.callback(new Object[]{"S2","\n"});
        workerCallback.callback(new Object[]{"S2", "Translation time: " + (endTranslate - startTranslate) + " ms\n"});
        workerCallback.callback(new Object[]{"S2","\n"});

        if(smtFormula != null)
        {
            final long startSolve   = System.currentTimeMillis();
            String smtResult        = solve(smtFormula, workerCallback);
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
                        workerCallback.callback(new Object[]{"S2","A model has been found\n"});
                        //construct A4Solution from smt result
                        StringBuilder SmtModel = new StringBuilder();
                        while(scanner.hasNext())
                        {
                            SmtModel.append(scanner.nextLine() + "\n");
                        }

                        SmtModel model = parseModel(SmtModel.toString());

                        writeModelToAlloyXmlFile(model, "1.smt.xml");

                        String  satResult           = "sat";
                        boolean isCounterExample    = false;
                        int expected                = -1;
                        String solutionXMLFile      = "1.smt.xml";
                        String formula              = "";

                        Object[]message = new Object []{satResult, isCounterExample, expected,
                                solutionXMLFile, formula, duration};
                        workerCallback.callback(message);

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

    private void writeModelToAlloyXmlFile(SmtModel model, String xmlFile) throws JAXBException
    {
        List<Signature> signatures = new ArrayList<>();

        Signature signature0 = new Signature();
        signature0.label = "seq/Int";
        signature0.id = 0;
        signature0.parentId = 1;
        signature0.builtIn = "yes";
        signatures.add(signature0);

        Signature signature1 = new Signature();
        signature1.label = "Int";
        signature1.id = 1;
        signature1.parentId = 2;
        signature1.builtIn = "yes";
        signatures.add(signature1);

        Signature signature2 = new Signature();
        signature2.label = "univ";
        signature2.id = 2;
        signature2.builtIn = "yes";
        signatures.add(signature2);

        Signature signature3  = new Signature();
        signature3.label = "String";
        signature3.id = 3;
        signature3.parentId = 2;
        signature3.builtIn = "yes";
        signatures.add(signature3);

        Atom atom0 = new Atom();
        atom0.label = "@uc_Atom_0";
        Atom atom1 = new Atom();
        atom1.label = "@uc_Atom_1";
        Atom atom2 = new Atom();
        atom2.label = "@uc_Atom_2";


        Signature signature4  = new Signature();
        signature4.atoms = new ArrayList<>();
        signature4.atoms.addAll(Arrays.asList(atom0, atom1, atom2));

        signature4.label = "this/A";
        signature4.id = 4;
        signature4.parentId = 2;
        signature4.builtIn = "no";

        signatures.add(signature4);

        Instance instance = new Instance();
        instance.signatures = signatures;
        instance.bitWidth = 4;
        instance.maxSeq = 4;
        instance.command = "Run Default for 4 but 4 int, 4 seq expect 0";

        instance.fileName = "C:\\temp\\smt\\alloy\\org.alloytools.alloy\\Untitled 1.als";

        Alloy alloy = new Alloy();
        alloy.instances = new ArrayList<>();
        alloy.instances.add(instance);

        JAXBContext context = JAXBContext.newInstance(Alloy.class);
        Marshaller m = context.createMarshaller();
        m.setProperty(Marshaller.JAXB_FORMATTED_OUTPUT, Boolean.TRUE);
        m.marshal(alloy, new File(xmlFile));

    }

    private String translateToSMT(WorkerEngine.WorkerCallback workerCallback)
    {
        //ToDo: implement the case when there are multiple files

        Iterator<Map.Entry<String, String>> iterator = alloyFiles.entrySet().iterator();

        Map.Entry<String, String> entry = iterator.next();

        String smtFormula = Utils.translateFromString(entry.getValue(), null);

        workerCallback.callback(new Object[]{"S2","Translation output:\n\n" + smtFormula + "\n"});

        return smtFormula;
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
