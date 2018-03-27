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

import java.util.LinkedHashSet;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.Attr;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Sig.PrimSig;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

/**
 * This class demonstrates how to access Alloy4 via the API, by modeling a
 * simple file system.
 */

public class DemoFileSystem {

    /*
     * Helper methods to simplify using the API for this example.
     */

    Set<Sig> sigs = new LinkedHashSet<Sig>();

    PrimSig makeSig(String name, boolean isAbstract, boolean isOne) throws Err {
        PrimSig ans = new PrimSig(name, (isAbstract ? Attr.ABSTRACT : null), (isOne ? Attr.ONE : null));
        sigs.add(ans);
        return ans;
    }

    PrimSig makeSig(PrimSig parent, String name, boolean isAbstract, boolean isOne) throws Err {
        PrimSig ans = new PrimSig(name, parent, (isAbstract ? Attr.ABSTRACT : null), (isOne ? Attr.ONE : null));
        sigs.add(ans);
        return ans;
    }

    void runFor3(Expr expr) throws Err {
        A4Options opt = new A4Options();
        Command cmd = new Command(false, 3, 3, 3, expr.and(fact));
        A4Solution sol = TranslateAlloyToKodkod.execute_command(NOP, sigs, cmd, opt);
        System.out.println(sol.toString().trim());
        if (sol.satisfiable()) {
            System.out.println("In particular, File = " + sol.eval(file));
            System.out.println("In particular, Dir = " + sol.eval(dir));
            System.out.println("In particular, contains = " + sol.eval(contains));
            System.out.println("In particular, parent = " + sol.eval(parent));
        }
        System.out.println();
    }

    /*
     * These corresponds to the helper predicates/functions provided in util/*.als
     */

    static Expr acyclic(Expr r) throws Err {
        Decl d = r.join(Sig.UNIV).oneOf("x"); // x is a variable over the domain
                                             // of r
        ExprHasName x = d.get();
        return x.in(x.join(r.closure())).not().forAll(d); // (x !in x.^r) for
                                                         // all x
    }

    /* Here are definitions common to all instances. */

    PrimSig obj    = null, dir = null, file = null, root = null;

    Field   parent = null, contains = null;

    Expr    fact   = ExprConstant.TRUE;

    void makeDomain() throws Err {
        // abstract sig Obj { parent: lone Dir }
        // abstract sig Dir extends Obj { contains: set Obj }
        // abstract sig File extends Obj { }
        // one sig Root extends Dir { }
        obj = makeSig("Obj", true, false);
        dir = makeSig(obj, "Dir", true, false);
        file = makeSig(obj, "File", true, false);
        root = makeSig(dir, "Root", false, true);
        parent = obj.addField("parent", dir.loneOf());
        contains = dir.addField("contains", obj.setOf());
        // fact { all x:Obj-Root | one x.parent }
        Decl x = obj.minus(root).oneOf("x");
        fact = x.get().join(parent).one().forAll(x).and(fact);
        // fact { contains = ~ parent }
        fact = contains.equal(parent.transpose()).and(fact);
        // fact { acyclic[contains] }
        fact = acyclic(contains).and(fact);
    }

    /* Here is instance number 1. */

    void makeInstance1() throws Err {
        // file = F1, F2, F3
        // dir = Root, D1, D2
        // F1.parent = D1
        // F2.parent = D2
        // F3.parent = D2
        // D2.parent = D1
        // D1.parent = Root
        PrimSig file1 = makeSig(file, "F1", false, true);
        PrimSig file2 = makeSig(file, "F2", false, true);
        PrimSig file3 = makeSig(file, "F3", false, true);
        PrimSig dir1 = makeSig(dir, "D1", false, true);
        PrimSig dir2 = makeSig(dir, "D2", false, true);
        fact = file1.join(parent).equal(dir1).and(fact);
        fact = file2.join(parent).equal(dir2).and(fact);
        fact = file3.join(parent).equal(dir2).and(fact);
        fact = dir2.join(parent).equal(dir1).and(fact);
        fact = dir1.join(parent).equal(root).and(fact);
    }

    /* Here is instance number 2. */

    void makeInstance2() throws Err {
        // dir = Root, D1, D2
        // D2.parent = D1
        // D1.parent = D2
        PrimSig dir1 = makeSig(dir, "D1", false, true);
        PrimSig dir2 = makeSig(dir, "D2", false, true);
        fact = dir2.join(parent).equal(dir1).and(fact);
        fact = dir1.join(parent).equal(dir2).and(fact);
    }

    private DemoFileSystem() {}

    /* The main driver. */

    public static void main(String[] args) throws Err {

        DemoFileSystem x;

        x = new DemoFileSystem();
        x.makeDomain();
        x.makeInstance1();
        x.runFor3(x.file.some()); // run { some file }

        x = new DemoFileSystem();
        x.makeDomain();
        x.makeInstance1();
        x.runFor3(acyclic(x.contains).not()); // run { !acyclic[contains] }
    }
}
