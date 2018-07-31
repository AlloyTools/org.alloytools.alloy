package tests.basic;

// Mincost not supported
/**
 * Tests the optimal-solution functionality provided by
 * {@link kodkod.engine.Solver#solve(Formula, Bounds, Cost) }.
 *
 * @author Emina Torlak
 */
// public class MinCostTest extends TestCase {
// private final int USIZE = 10;
// private final TupleFactory factory;
// private final Solver solver;
// private final Relation ra, rb, rab, rba;
// private final Bounds bounds;
// private final Cost cost;
// private final Map<Relation, Integer> cmap;
//
// public MinCostTest(String arg0) {
// super(arg0);
// this.solver = new Solver();
// solver.options().setSolver(SATFactory.ZChaffMincost);
// List<String> atoms = new ArrayList<String>(USIZE);
// for (int i = 0; i < USIZE; i++) {
// atoms.add(""+i);
// }
// final Universe universe = new Universe(atoms);
// this.factory = universe.factory();
// this.ra = Relation.unary("ra");
// this.rb = Relation.unary("rb");
// this.rab = Relation.binary("rab");
// this.rba = Relation.binary("rba");
// this.bounds = new Bounds(universe);
// this.cmap = new LinkedHashMap<Relation, Integer>();
// cmap.put(ra, 1);
// cmap.put(rb, 2);
// cmap.put(rab, 4);
// cmap.put(rba, 8);
// this.cost = new Cost() {
// public int edgeCost(Relation relation) {
// return cmap.containsKey(relation) ? cmap.get(relation) : 0;
// }
// };
// }
//
// protected void setUp() throws Exception {
// super.setUp();
// bounds.bound(ra, factory.setOf("0","1","2","3","4"));
// bounds.bound(rb, factory.setOf("5","6","7","8","9"));
// bounds.bound(rab, bounds.upperBound(ra).product(bounds.upperBound(rb)));
// bounds.bound(rba, bounds.upperBound(rb).product(bounds.upperBound(ra)));
// }
//
// private Solution solve(Formula formula) {
//
// return solver.solve(formula, bounds, cost);
//
// }
//
// private Solution solve(Formula formula, Bounds bounds) {
//
// return solver.solve(formula, bounds, cost);
//
// }
//
//// private Solution simpleSolve(Formula formula) {
//// try {
//// solver.options().setSolver(SATFactory.ZChaffBasic);
//// return solver.solve(formula, bounds);
//// } catch (TimeoutException te) {
//// fail("Timed out solving " + formula);
//// return null;
//// }
//// }
//
// public void testNoSolution() {
// Formula f = ra.some().and(rab.no()).and(ra.in(Expression.UNIV.join(rab)));
// Solution s = solve(f);
// assertEquals(Solution.Outcome.UNSATISFIABLE, s.outcome());
// }
//
// public void testOneSolution() {
// final examples.sudoku.Sudoku model = new Sudoku(3);
// final Solution sol = solve(model.rules(),
// model.bounds(Sudoku.defaultPuzzle()));
// assertEquals(Solution.Outcome.SATISFIABLE, sol.outcome());
// }
//
// public void testMultipleSolutions() {
// Formula f = ra.some().or(rb.some()).or(rab.some()).or(rba.some());
// Solution s = solve(f);
// assertEquals(Solution.Outcome.SATISFIABLE, s.outcome());
// assertEquals(1, s.instance().tuples(ra).size());
// assertEquals(0, s.instance().tuples(rb).size());
// assertEquals(0, s.instance().tuples(rab).size());
// assertEquals(0, s.instance().tuples(rba).size());
// }
// }
