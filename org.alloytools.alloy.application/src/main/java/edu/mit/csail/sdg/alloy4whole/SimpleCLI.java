/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.alloy4whole;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.RandomAccessFile;
import java.io.StringReader;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4.Version;
import edu.mit.csail.sdg.alloy4.XMLNode;
import edu.mit.csail.sdg.alloy4viz.StaticInstanceReader;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Options.SatSolver;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.A4SolutionReader;
import edu.mit.csail.sdg.translator.A4SolutionWriter;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

/**
 * This class is used by the Alloy developers to drive the regression test
 * suite. For a more detailed guide on how to use Alloy API, please see
 * "ExampleUsingTheCompiler.java"
 *
 * @modified [electrum] updated reporting
 */
public final class SimpleCLI {

    private static final class SimpleReporter extends A4Reporter {

        private final StringBuilder      sb       = new StringBuilder();

        private final List<ErrorWarning> warnings = new ArrayList<ErrorWarning>();

        private final RandomAccessFile   os;

        public SimpleReporter() throws IOException {
            os = new RandomAccessFile(".alloy.tmp", "rw");
            os.setLength(0);
        }

        public void flush() throws IOException {
            if (sb.length() > 65536) {
                os.write(sb.toString().getBytes("UTF-8"));
                sb.delete(0, sb.length());
            }
        }

        public void close() throws IOException {
            if (sb.length() > 0) {
                os.write(sb.toString().getBytes("UTF-8"));
                sb.delete(0, sb.length());
            }
            os.close();
        }

        @Override
        public void debug(String msg) {
            sb.append(msg);
        }

        @Override
        public void parse(String msg) {
            sb.append(msg);
        }

        @Override
        public void typecheck(String msg) {
            sb.append(msg);
        }

        @Override
        public void warning(ErrorWarning msg) {
            warnings.add(msg);
        }

        @Override
        public void scope(String msg) {
            sb.append("   ");
            sb.append(msg);
        }

        @Override
        public void bound(String msg) {
            sb.append("   ");
            sb.append(msg);
        }

        @Override
        public void translate(String solver, int bitwidth, int maxseq, int mintrace, int maxtrace, int skolemDepth, int symmetry, String strat) {
            debug("Solver=" + solver + (maxtrace < 1 ? "" : " Steps=" + mintrace + ".." + maxtrace) + " Bitwidth=" + bitwidth + " MaxSeq=" + maxseq + " Symmetry=" + (symmetry > 0 ? ("" + symmetry) : "OFF") + " Mode=" + strat + "\n");
        }

        @Override
        public void solve(int step, int primaryVars, int totalVars, int clauses) {
            if (db)
                db("   " + totalVars + " vars. " + primaryVars + " primary vars. " + clauses + " clauses.\n");
            sb.append("   " + totalVars + " vars. " + primaryVars + " primary vars. " + clauses + " clauses. 12345ms.\n");
        }

        @Override
        public void resultCNF(String filename) {}

        @Override
        public void resultSAT(Object command, long solvingTime, Object solution) {
            if (db)
                db("   SAT!\n");
            if (!(command instanceof Command))
                return;
            Command cmd = (Command) command;
            sb.append(cmd.check ? "   Counterexample found. " : "   Instance found. ");
            if (cmd.check)
                sb.append("Assertion is invalid");
            else
                sb.append("Predicate is consistent");
            if (cmd.expects == 0)
                sb.append(", contrary to expectation");
            else if (cmd.expects == 1)
                sb.append(", as expected");
            sb.append(". " + solvingTime + "ms.\n\n");
        }

        @Override
        public void resultUNSAT(Object command, long solvingTime, Object solution) {
            if (db)
                db("   UNSAT!\n");
            if (!(command instanceof Command))
                return;
            Command cmd = (Command) command;
            sb.append(cmd.check ? "   No counterexample found." : "   No instance found.");
            if (cmd.check)
                sb.append(" Assertion may be valid");
            else
                sb.append(" Predicate may be inconsistent");
            if (cmd.expects == 1)
                sb.append(", contrary to expectation");
            else if (cmd.expects == 0)
                sb.append(", as expected");
            sb.append(". " + solvingTime + "ms.\n\n");
        }
    }

    private static boolean db = true;

    private static void db(String msg) {
        System.out.print(msg);
        System.out.flush();
    }

    private SimpleCLI() {}

    private static void validate(A4Solution sol) throws Exception {
        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        sol.writeXML(pw, null, null);
        pw.flush();
        sw.flush();
        String txt = sw.toString();
        A4SolutionReader.read(new ArrayList<Sig>(), new XMLNode(new StringReader(txt))).toString();
        StaticInstanceReader.parseInstance(new StringReader(txt), 0);
    }

    public static void main(String[] args) throws Exception {
        final boolean sat4j = "yes".equals(System.getProperty("sat4j"));
        final boolean minisat = "yes".equals(System.getProperty("minisat"));
        SatSolver solver = A4Options.SatSolver.make("mem", "mem", "/zweb/sat/mem");
        final SimpleReporter rep = new SimpleReporter();
        final StringBuilder sb = rep.sb;
        for (String filename : args) {
            try {
                // Parse+Typecheck
                rep.sb.append("\n\nMain file = " + filename + "\n");
                if (db)
                    db("Parsing+Typechecking...");
                Module world = CompUtil.parseEverything_fromFile(rep, null, filename);
                if (db)
                    db(" ok\n");
                List<Command> cmds = world.getAllCommands();
                for (ErrorWarning msg : rep.warnings)
                    rep.sb.append("Relevance Warning:\n" + (msg.toString().trim()) + "\n\n");
                rep.warnings.clear();
                // Do a detailed dump if we will not be executing the commands
                if (args.length != 1) {
                    for (Module m : world.getAllReachableModules()) {
                        for (Sig x : m.getAllSigs()) {
                            sb.append("\nSig ").append(x.label).append(" at position ").append(x.pos).append("\n");
                            for (Decl d : x.getFieldDecls())
                                for (ExprHasName f : d.names) {
                                    sb.append("\nField ").append(f.label).append(" with type ").append(f.type()).append("\n");
                                    d.expr.toString(sb, 2);
                                }
                            rep.flush();
                        }
                        for (Func x : m.getAllFunc()) {
                            sb.append("\nFun/pred ").append(x.label).append(" at position ").append(x.pos).append("\n");
                            for (Decl d : x.decls)
                                for (ExprHasName v : d.names) {
                                    v.toString(sb, 2);
                                    d.expr.toString(sb, 4);
                                }
                            x.returnDecl.toString(sb, 2);
                            x.getBody().toString(sb, 4);
                            rep.flush();
                        }
                        for (Pair<String,Expr> x : m.getAllFacts()) {
                            sb.append("\nFact ").append(x.a).append("\n");
                            x.b.toString(sb, 4);
                            rep.flush();
                        }
                        for (Pair<String,Expr> x : m.getAllAssertions()) {
                            sb.append("\nAssertion ").append(x.a).append("\n");
                            x.b.toString(sb, 4);
                            rep.flush();
                        }
                        if (m == world)
                            for (Command x : m.getAllCommands()) {
                                sb.append("\nCommand ").append(x.label).append("\n");
                                x.formula.toString(sb, 4);
                                rep.flush();
                            }
                    }
                    continue;
                }
                // Validate the metamodel generation code
                StringWriter metasb = new StringWriter();
                PrintWriter meta = new PrintWriter(metasb);
                Util.encodeXMLs(meta, "\n<alloy builddate=\"", Version.buildDate(), "\">\n\n");
                A4SolutionWriter.writeMetamodel(world.getAllReachableSigs(), filename, meta);
                Util.encodeXMLs(meta, "\n</alloy>");
                meta.flush();
                metasb.flush();
                String metaxml = metasb.toString();
                A4SolutionReader.read(new ArrayList<Sig>(), new XMLNode(new StringReader(metaxml)));
                StaticInstanceReader.parseInstance(new StringReader(metaxml), 0);
                // Okay, now solve the commands
                A4Options options = new A4Options();
                options.originalFilename = filename;
                options.solverDirectory = "/zweb/zweb/tmp/alloy4/x86-freebsd";
                options.solver = sat4j ? A4Options.SatSolver.SAT4J : (minisat ? A4Options.SatSolver.MiniSatJNI : solver);
                for (int i = 0; i < cmds.size(); i++) {
                    Command c = cmds.get(i);
                    if (db) {
                        String cc = c.toString();
                        if (cc.length() > 60)
                            cc = cc.substring(0, 55);
                        db("Executing " + cc + "...\n");
                    }
                    rep.sb.append("Executing \"" + c + "\"\n");
                    options.skolemDepth = 0;
                    A4Solution s = TranslateAlloyToKodkod.execute_commandFromBook(rep, world.getAllReachableSigs(), c, options);
                    if (s.satisfiable()) {
                        validate(s);
                        if (s.isIncremental()) {
                            s = s.next();
                            if (s.satisfiable())
                                validate(s);
                        }
                    }
                    options.skolemDepth = 2;
                    s = TranslateAlloyToKodkod.execute_commandFromBook(rep, world.getAllReachableSigs(), c, options);
                    if (s.satisfiable()) {
                        validate(s);
                        if (s.isIncremental()) {
                            s = s.next();
                            if (s.satisfiable())
                                validate(s);
                        }
                    }
                }
            } catch (Throwable ex) {
                rep.sb.append("\n\nException: " + ex);
            }
            if (db) {
                if (args.length != 1)
                    db(" ERROR!\n");
                else
                    db("\n\n");
            }
        }
        rep.close();
    }
}
