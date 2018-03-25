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

import static edu.mit.csail.sdg.alloy4.A4Reporter.NOP;
import static edu.mit.csail.sdg.ast.Sig.UNIV;

import java.util.Arrays;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.ast.Attr;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.PrimSig;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

/**
 * This class demonstrates how to access Alloy4 via the API.
 */

public final class ExampleUsingTheAPI {

    public static void main(String[] args) throws Err {

        // Chooses the Alloy4 options
        A4Options opt = new A4Options();
        opt.solver = A4Options.SatSolver.SAT4J;

        // abstract sig A {}
        PrimSig A = new PrimSig("A", Attr.ABSTRACT);

        // sig B {}
        PrimSig B = new PrimSig("B");

        // one sig A1 extends A {}
        PrimSig A1 = new PrimSig("A1", A, Attr.ONE);

        // one sig A2 extends A {}
        PrimSig A2 = new PrimSig("A2", A, Attr.ONE);

        // A { f: B lone->lone B }
        Expr f = A.addField("f", B.lone_arrow_lone(B));
        // Since (B lone->lone B) is not unary, the default is "setOf", meaning
        // "f:set (B lone->lone B)"

        // A { g: B }
        Expr g = A.addField("g", B);
        // The line above is the same as: A.addField(null, "g", B.oneOf()) since
        // B is unary.
        // If you want "setOf", you need: A.addField(null, "g", B.setOf())

        // pred someG { some g }
        Func someG = new Func(null, "SomeG", null, null, g.some());

        // pred atMostThree[x:univ, y:univ] { #(x+y) >= 3 }
        Decl x = UNIV.oneOf("x");
        Decl y = UNIV.oneOf("y");
        Expr body = x.get().plus(y.get()).cardinality().lte(ExprConstant.makeNUMBER(3));
        Func atMost3 = new Func(null, "atMost3", Util.asList(x, y), null, body);

        List<Sig> sigs = Arrays.asList(new Sig[] {
                                                  A, B, A1, A2
        });

        // run { some A && atMostThree[B,B] } for 3 but 3 int, 3 seq
        Expr expr1 = A.some().and(atMost3.call(B, B));
        Command cmd1 = new Command(false, 3, 3, 3, expr1);
        A4Solution sol1 = TranslateAlloyToKodkod.execute_command(NOP, sigs, cmd1, opt);
        System.out.println("[Solution1]:");
        System.out.println(sol1.toString());

        // run { some f && SomeG[] } for 3 but 2 int, 1 seq, 5 A, exactly 6 B
        Expr expr2 = f.some().and(someG.call());
        Command cmd2 = new Command(false, 3, 2, 1, expr2);
        cmd2 = cmd2.change(A, false, 1);
        cmd2 = cmd2.change(B, true, 1);
        A4Solution sol2 = TranslateAlloyToKodkod.execute_command(NOP, sigs, cmd2, opt);

        while (sol2.satisfiable()) {
            System.out.println("[Solution2]:");
            System.out.println(sol2.toString());
            sol2 = sol2.next();
        }
    }
}
