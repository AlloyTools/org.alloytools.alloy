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

import java.io.StringReader;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.Arrays;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.MailBug;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.alloy4.XMLNode;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.A4SolutionReader;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;
import junit.framework.TestCase;

/**
 * API-specific regression test suite; the larger collection of models that test
 * both the compiler and translator are in models/tests/*.als
 */

public class InternalTest extends TestCase {

    private static void check(boolean condition) throws Exception {
        if (!condition)
            throw new RuntimeException("Assertion failure: condition should be TRUE");
    }

    private static void check(Object a, Object b) {
        if (a == null) {
            if (b != null)
                throw new AssertionError("a is null, but b is " + b);
        } else if (b == null) {
            throw new AssertionError("b is null, but a is " + a);
        } else if (!a.equals(b)) {
            throw new AssertionError("a!=b\n" + "a=" + a + "\nb=" + b + "\n");
        }
    }

    public void test1() throws Exception {
        XMLNode xml = new XMLNode(new StringReader("<alloy builddate='unknown'>" + "<instance bitwidth='2' maxseq='1' command='Run Deadlock' filename='dijkstra.als'>" + "<sig label='univ' ID='0' builtin='yes'> <atom label='-2'/> <atom label='-1'/> <atom label='0'/> <atom label='1'/> <atom label='State$0'/> <atom label='State$1'/> <atom label='State$2'/> </sig>" + "<sig label='Int' ID='1' parentID='0' builtin='yes'> <atom label='-2'/> <atom label='-1'/> <atom label='0'/> <atom label='1'/> </sig>" + "<sig label='seq/Int' ID='2' parentID='1' builtin='yes'> <atom label='0'/> </sig>" + "<sig label='State' ID='5' parentID='0'> <atom label='State$0'/> <atom label='State$1'/> <atom label='State$2'/> </sig>" + "<field label='len' parentID='5' ID='17'>" + "   <tuple> <atom label='State$1'/> <atom label='-2'/> </tuple>" + "   <tuple> <atom label='State$1'/> <atom label='-1'/> </tuple>" + "   <types> <type ID='5'/> <type ID='1'/> </types>" + "</field>" + "<skolem label='$Deadlock_s' ID='16'>" + "   <tuple> <atom label='State$0'/> </tuple>" + "   <types> <type ID='5'/> </types>" + "</skolem>" + "</instance>" + "</alloy>"));
        Sig state = new Sig.PrimSig("State");
        A4Solution sol = A4SolutionReader.read(Arrays.asList(state), xml);
        SafeList<ExprVar> skolems = new SafeList<ExprVar>(sol.getAllSkolems());
        check(skolems.size() == 1);
        check(skolems.get(0).label, "$Deadlock_s");
        check(skolems.get(0).type(), state.type());
        //
        Sig state2 = new Sig.PrimSig("State");
        Field field2 = state2.addField("len", Sig.SIGINT);
        sol = A4SolutionReader.read(Arrays.asList(state2), xml);
        SafeList<ExprVar> skolems2 = new SafeList<ExprVar>(sol.getAllSkolems());
        check(skolems2.size() == 1);
        check(skolems2.get(0).label, "$Deadlock_s");
        check(skolems2.get(0).type(), state2.type());
        check("" + sol.eval(field2.cardinality()), "-2");
    }

    public void test2() throws Exception {
        test1();
        XMLNode xml = new XMLNode(new StringReader("<alloy builddate='unknown'>" + "<instance bitwidth='2' maxseq='1' command='Run Deadlock' filename='dijkstra.als'>" + "<sig label='univ' ID='0' builtin='yes'> <atom label='-2'/> <atom label='-1'/> <atom label='0'/> <atom label='1'/> <atom label='State$0'/> <atom label='State$1'/> <atom label='State$2'/> </sig>" + "<sig label='Int' ID='1' parentID='0' builtin='yes'> <atom label='-2'/> <atom label='-1'/> <atom label='0'/> <atom label='1'/> </sig>" + "<sig label='seq/Int' ID='2' parentID='1' builtin='yes'> <atom label='0'/> </sig>" + "<sig label='Act' ID='5' parentID='0'> <atom label='Act$0'/> <atom label='Act$1'/> <atom label='Act$2'/> </sig>" + "<skolem label='$x' ID='16'>" + "   <tuple> <atom label='0'/> <atom label='Act$1'/> </tuple>" + "   <types> <type ID='2'/> <type ID='5'/> </types>" + "</skolem>" + "</instance>" + "</alloy>"));
        Sig activity = new Sig.PrimSig("Act");
        A4Solution sol = A4SolutionReader.read(Arrays.asList(activity), xml);
        SafeList<ExprVar> skolems = new SafeList<ExprVar>(sol.getAllSkolems());
        check(skolems.size() == 1);
        check(skolems.get(0).label, "$x");
        check(skolems.get(0).type(), Sig.SEQIDX.type().product(activity.type()));
    }

    public void test3() throws Exception {
        XMLNode xml = new XMLNode(new StringReader("<alloy builddate='unknown'>" + "<instance bitwidth='2' maxseq='1' command='Run Deadlock' filename='dijkstra.als'>" + "<sig label='univ' ID='0' builtin='yes'> <atom label='-2'/> <atom label='-1'/> <atom label='0'/> <atom label='1'/> <atom label='State$0'/> <atom label='State$1'/> <atom label='State$2'/> </sig>" + "<sig label='Int' ID='1' parentID='0' builtin='yes'> <atom label='-2'/> <atom label='-1'/> <atom label='0'/> <atom label='1'/> </sig>" + "<sig label='seq/Int' ID='2' parentID='1' builtin='yes'> <atom label='0'/> </sig>" + "<sig label='State' ID='5' parentID='6'> <atom label='State$0'/> </sig>" + "<sig label='Mutex' ID='6' parentID='5'> <atom label='Mutex$0'/> </sig>" + "</instance>" + "</alloy>"));
        String err = "";
        try {
            A4SolutionReader.read(null, xml);
        } catch (Throwable ex) {
            err = ex.toString();
        }
        check(err.contains("cyclic inheritance"));
    }

    /**
     * Displays the amount of memory taken per solution enumeration.
     */
    public static void main2(String[] args) throws Exception {
        String filename = "models/examples/algorithms/dijkstra.als";
        Module world = CompUtil.parseEverything_fromFile(A4Reporter.NOP, null, filename);
        A4Options options = new A4Options();
        for (Command command : world.getAllCommands()) {
            A4Solution ans = TranslateAlloyToKodkod.execute_command(A4Reporter.NOP, world.getAllReachableSigs(), command, options);
            while (ans.satisfiable()) {
                String hc = "Answer: " + ans.toString().hashCode();
                System.gc();
                System.gc();
                System.gc();
                Thread.sleep(500);
                System.gc();
                System.gc();
                System.gc();
                Thread.sleep(500);
                long t = Runtime.getRuntime().totalMemory(), f = Runtime.getRuntime().freeMemory(),
                                m = Runtime.getRuntime().maxMemory();
                System.out.println(hc + " total=" + t + " free=" + f + " max=" + m);
                System.out.flush();
                ans = ans.next();
            }
            return;
        }
    }

    /** Runs every test case. */
    public static void main(String[] args) throws Exception {
        try {
            for (Method m : InternalTest.class.getDeclaredMethods()) {
                String name = m.getName();
                if (name.startsWith("test")) {
                    System.out.print("Running " + name + "...");
                    System.out.flush();
                    m.invoke(null, new Object[0]);
                    System.out.print(" Done.\n");
                    System.out.flush();
                }
            }
        } catch (Throwable ex) {
            while (ex instanceof InvocationTargetException)
                ex = ((InvocationTargetException) ex).getCause();
            System.out.println();
            System.out.flush();
            System.err.println("Error:\n" + MailBug.dump(ex).trim() + "\n");
            System.err.flush();
            System.exit(1);
        }
    }
}
