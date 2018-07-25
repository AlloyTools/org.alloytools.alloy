package examples.alloy;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Decls;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 * A kodkod encoding of John McCarthy's thoughnut problem
 *
 * <pre>
 * module internal/tougnut
 *
 * open util/ordering[Cell]
 *
 * sig Cell { covered: Cell -> Cell -> Cell }
 *
 * pred covering() {
 * // opposite corners not on the board
 * let board = Cell->Cell - (first()->first() + last()->last()) |
 *   covered in board->board
 *
 * // covering relation is symmetric
 * all x,y: Cell | y.(x.covered)->x->y in covered
 *
 * // each pair of cells on the board should be covered
 * // by a domino, which also covers ONE of its neighbors
 *  all x,y: Cell | one y.(x.covered) &&
 *   y.(x.covered) in  (prev(x)+next(x))->y + x->(prev(y) + next(y))
 *  }
 * </pre>
 *
 * @author Emina
 */
public final class Toughnut {

    private final Relation Cell, covered, ord;

    /**
     * Creates an instance of Toughnut.
     */
    public Toughnut() {
        this.Cell = Relation.unary("Cell");
        this.covered = Relation.nary("covered", 4);
        this.ord = Relation.binary("ord");
    }

    private Expression next(Expression e) {
        return e.join(ord);
    }

    private Expression prev(Expression e) {
        return ord.join(e);
    }

    /**
     * Returns the covering predicate. Note that we don't need to specify the first
     * two lines of the predicate, since they can be expressed as bounds
     * constraints.
     *
     * @return the covering predicate
     */
    public Formula checkBelowTooDoublePrime() {
        final Variable x = Variable.unary("x");
        final Variable y = Variable.unary("y");
        final Decls d = x.oneOf(Cell).and(y.oneOf(Cell));
        final Expression xy = y.join(x.join(covered));
        // covering relation is symmetric
        Formula symm = xy.product(x.product(y)).in(covered).forAll(d);
        // each pair of cells on the board should be covered
        // by a domino, which also covers ONE of its neighbors
        Expression xNeighbors = (prev(x).union(next(x))).product(y);
        Expression yNeighbors = x.product(prev(y).union(next(y)));
        Formula covering = (xy.one().and(xy.in(xNeighbors.union(yNeighbors)))).forAll(d);
        return symm.and(covering);
    }

    /**
     * Returns bounds for an nxn board.
     *
     * @return bounds for an nxn board.
     */
    public Bounds bounds(int n) {
        assert n > 0;
        final List<String> atoms = new ArrayList<String>(n);
        for (int i = 0; i < n; i++) {
            atoms.add(String.valueOf(i));
        }
        final Universe u = new Universe(atoms);
        final Bounds b = new Bounds(u);
        final TupleFactory f = u.factory();

        b.boundExactly(Cell, f.allOf(1));

        final TupleSet ordBound = f.noneOf(2);
        for (int i = 0; i < n - 1; i++) {
            ordBound.add(f.tuple(String.valueOf(i), String.valueOf(i + 1)));
        }
        b.boundExactly(ord, ordBound);

        final TupleSet board = f.allOf(2);
        board.remove(f.tuple(String.valueOf(0), String.valueOf(0)));
        board.remove(f.tuple(String.valueOf(n - 1), String.valueOf(n - 1)));

        b.bound(covered, board.product(board));

        return b;
    }

    /**
     * Usage: java examples.Toughnut [size of one side of the board; optional]
     */
    public static void main(String[] args) {
        try {
            int n = args.length == 0 ? 4 : Integer.parseInt(args[0]);
            final Toughnut nut = new Toughnut();
            final Solver solver = new Solver();
            solver.options().setSolver(SATFactory.MiniSat);
            final Formula covering = nut.checkBelowTooDoublePrime();
            final Bounds bounds = nut.bounds(n);

            // System.out.println(covering);
            // System.out.println(bounds);
            final Solution sol = solver.solve(covering, bounds);
            System.out.println(sol);
        } catch (NumberFormatException nfe) {
            System.out.println("Usage: java examples.Toughnut [size of one side of the board; optional]");
        }

    }
}
