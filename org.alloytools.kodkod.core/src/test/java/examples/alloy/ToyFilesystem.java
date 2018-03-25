/*
 * Kodkod -- Copyright (c) 2005-2008, Emina Torlak
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package examples.alloy;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.Universe;
import kodkod.util.nodes.PrettyPrinter;

/**
 * A toy filesystem specification.
 *
 * @author Emina Torlak
 */
public final class ToyFilesystem {

    private final Relation file, dir, root;
    private final Relation contents;

    /**
     * Constructs a new instance of the file system problem.
     */
    public ToyFilesystem() {
        file = Relation.unary("File");
        dir = Relation.unary("Dir");
        root = Relation.unary("Root");
        contents = Relation.binary("contents");
    }

    /**
     * Returns the toy filesystem constraints
     *
     * @return toy filesystem constraints
     */
    public Formula constraints() {
        final List<Formula> formulas = new ArrayList<Formula>();

        formulas.add(contents.in(dir.product(dir.union(file))));

        final Variable d = Variable.unary("d");
        formulas.add(d.in(d.join(contents.closure())).not().forAll(d.oneOf(dir)));

        formulas.add(root.in(dir));

        formulas.add(file.union(dir).in(root.join(contents.reflexiveClosure())));

        return Formula.and(formulas);
    }

    /**
     * Returns the toy filesystem bounds.
     *
     * @return toy filesystem bounds
     */
    public final Bounds bounds() {
        final Universe universe = new Universe("d0", "d1", "f0", "f1", "f2");
        final Bounds bounds = new Bounds(universe);
        final TupleFactory factory = universe.factory();
        bounds.boundExactly(root, factory.setOf("d0"));
        bounds.bound(dir, factory.setOf("d0", "d1"));
        bounds.bound(file, factory.setOf("f0", "f1", "f2"));
        bounds.bound(contents, factory.setOf(factory.tuple("d0", "d1")), bounds.upperBound(dir).product(factory.allOf(1)));
        return bounds;
    }

    /**
     * Usage: java examples.alloy.ToyFilesystem
     */
    public static void main(String[] args) {
        final ToyFilesystem toy = new ToyFilesystem();
        final Formula f = toy.constraints();
        System.out.println(PrettyPrinter.print(f, 2));
        final Bounds b = toy.bounds();
        final Solver solver = new Solver();
        solver.options().setSolver(SATFactory.MiniSat);

        final Solution s = solver.solve(f, b);
        System.out.println(s);
    }
}
