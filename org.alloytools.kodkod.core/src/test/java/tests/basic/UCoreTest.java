/**
 *
 */
package tests.basic;

import junit.framework.TestCase;

/**
 * Tests the unsat core functionality.
 *
 * @author Emina Torlak
 */
public final class UCoreTest extends TestCase {

    public void test() {}

    // private static final Class< ? >[] FIXED_SCOPE = {
    // NUM378.class
    // };
    //
    // // scopes 1-5
    // private static final Class< ? >[] EASY = {
    // Toughnut.class, MED007.class, MED009.class,
    // };
    //
    // // scopes 1-4
    // private static final Class< ? >[] MEDIUM = {
    // Lists.class, Trees.class, Hotel.class, RingElection.class, COM008.class,
    // TOP020.class, GEO091.class,
    // GEO092.class, GEO115.class, GEO158.class, GEO159.class, LAT258.class,
    // };
    //
    // // scopes 1-3
    // private static final Class< ? >[] HARD = {
    // ALG212.class, NUM374.class, SET943.class, SET948.class, SET967.class,
    // };
    //
    // private static final int EASY_MAX = 5, MED_MAX = 4, HARD_MAX = 3;
    //
    // private final Solver solver;
    // private final Solver vSolver;
    //
    // public UCoreTest() {
    // solver = new Solver();
    // solver.options().setLogTranslation(1);
    // solver.options().setSolver(SATFactory.MiniSatProver);
    // vSolver = new Solver();
    // vSolver.options().setSolver(SATFactory.MiniSat);
    // }
    //
    // private final void verify(Set<Formula> core, Bounds bounds) {
    // // check that the conjunction of the high-level core formulas is false
    // assertNull(vSolver.solve(Formula.and(core), bounds).instance());
    //
    // // check that the core is minimal
    // final Set<Formula> tmpCore = new LinkedHashSet<Formula>(core);
    // for (Iterator<Formula> itr = core.iterator(); itr.hasNext();) {
    // final Formula f = itr.next();
    // tmpCore.remove(f);
    // assertNotNull(vSolver.solve(Formula.and(tmpCore), bounds).instance());
    // tmpCore.add(f);
    // }
    //
    // }
    //
    // private final void minimizeAndVerify(Formula formula, Bounds bounds,
    // Proof proof, ReductionStrategy strategy) {
    // proof.minimize(strategy);
    // final Set<Formula> core = Nodes.allRoots(formula,
    // proof.highLevelCore().values());
    // final Set<Formula> tcore = proof.highLevelCore().keySet();
    // verify(tcore, proof.log().bounds());
    // if (solver.options().coreGranularity() == 0) {
    // assertEquals(tcore.size(), core.size());
    // verify(core, bounds);
    // } else {
    // assertNull(vSolver.solve(Formula.and(core), bounds).instance());
    // }
    // }
    //
    // private final void testTrivialProofExtractor(Class< ? >[] probs, int
    // maxScope) {
    // for (Class< ? > prob : probs) {
    // Object instance = UCoreStats.instance(prob);
    // Map<Method,Formula> checks = invokeAll(instance, checks(prob));
    // for (Formula check : checks.values()) {
    // for (int scope = 1; scope <= maxScope; scope++) {
    // Bounds bounds = bounds(instance, scope);
    // Solution sol = solver.solve(check, bounds);
    // if (sol.outcome() == Solution.Outcome.TRIVIALLY_UNSATISFIABLE) {
    // minimizeAndVerify(check, bounds, sol.proof(), null);
    // } else {
    // break;
    // }
    // }
    // }
    //
    // }
    // }
    //
    // private final void testTrivialProofExtractor(Class< ? >[] probs) {
    // for (Class< ? > prob : probs) {
    // Object instance = UCoreStats.instance(prob);
    // Map<Method,Formula> checks = invokeAll(instance, checks(prob));
    // for (Formula check : checks.values()) {
    // Bounds bounds = bounds(instance);
    // Solution sol = solver.solve(check, bounds);
    // if (sol.outcome() == Solution.Outcome.TRIVIALLY_UNSATISFIABLE) {
    // minimizeAndVerify(check, bounds, sol.proof(), null);
    // }
    // }
    //
    // }
    // }
    //
    // private final void testProofExtractor(Class< ? >[] probs, Class< ?
    // extends ReductionStrategy> strategy,
    // int maxScope) {
    // System.out.println("" + Arrays.toString(probs) + " " + strategy + " " +
    // maxScope);
    //
    // for (Class< ? > prob : probs) {
    // Object instance = UCoreStats.instance(prob);
    // Map<Method,Formula> checks = invokeAll(instance, checks(prob));
    // for (Formula check : checks.values()) {
    // for (int scope = 1; scope <= maxScope; scope++) {
    // Bounds bounds = bounds(instance, scope);
    // Solution sol = solver.solve(check, bounds);
    // if (sol.outcome() == Solution.Outcome.UNSATISFIABLE) {
    // minimizeAndVerify(check, bounds, sol.proof(), strategy(strategy,
    // sol.proof().log()));
    // }
    // }
    // }
    //
    // }
    // System.out.println("done");
    // }
    //
    // private final void testProofExtractor(Class< ? >[] probs, Class< ?
    // extends ReductionStrategy> strategy) {
    // for (Class< ? > prob : probs) {
    // Object instance = UCoreStats.instance(prob);
    // Map<Method,Formula> checks = invokeAll(instance, checks(prob));
    // for (Formula check : checks.values()) {
    // Bounds bounds = bounds(instance);
    // Solution sol = solver.solve(check, bounds);
    // if (sol.outcome() == Solution.Outcome.UNSATISFIABLE) {
    // minimizeAndVerify(check, bounds, sol.proof(), strategy(strategy,
    // sol.proof().log()));
    // }
    // }
    //
    // }
    // }
    //
    // public final void testFixedTrivial0() {
    // solver.options().setCoreGranularity(0);
    // testTrivialProofExtractor(FIXED_SCOPE);
    // testTrivialProofExtractor(EASY, EASY_MAX);
    // testTrivialProofExtractor(MEDIUM, MED_MAX);
    // testTrivialProofExtractor(HARD, HARD_MAX);
    // }
    //
    // public final void testFixedTrivial1() {
    // solver.options().setCoreGranularity(1);
    // testTrivialProofExtractor(FIXED_SCOPE);
    // testTrivialProofExtractor(EASY, EASY_MAX);
    // testTrivialProofExtractor(MEDIUM, MED_MAX);
    // testTrivialProofExtractor(HARD, HARD_MAX);
    // }
    //
    // public final void testFixedTrivial2() {
    // solver.options().setCoreGranularity(2);
    // testTrivialProofExtractor(FIXED_SCOPE);
    // testTrivialProofExtractor(EASY, EASY_MAX);
    // testTrivialProofExtractor(MEDIUM, MED_MAX);
    // testTrivialProofExtractor(HARD, HARD_MAX);
    // }
    //
    // public final void testFixedTrivial3() {
    // solver.options().setCoreGranularity(3);
    // testTrivialProofExtractor(FIXED_SCOPE);
    // testTrivialProofExtractor(EASY, EASY_MAX);
    // testTrivialProofExtractor(MEDIUM, MED_MAX);
    // testTrivialProofExtractor(HARD, HARD_MAX);
    // }
    //
    // public final void testFixedSCE0() {
    // solver.options().setCoreGranularity(0);
    // testProofExtractor(FIXED_SCOPE, SCEStrategy.class);
    // }
    //
    // public final void testEasySCE0() {
    // solver.options().setCoreGranularity(0);
    // testProofExtractor(EASY, SCEStrategy.class, EASY_MAX);
    // }
    //
    // public final void testMediumSCE0() {
    // solver.options().setCoreGranularity(0);
    // testProofExtractor(MEDIUM, SCEStrategy.class, MED_MAX);
    // }
    //
    // public final void testHardSCE0() {
    // solver.options().setCoreGranularity(0);
    // testProofExtractor(HARD, SCEStrategy.class, HARD_MAX);
    // }
    //
    // public final void testFixedSCE1() {
    // solver.options().setCoreGranularity(1);
    // testProofExtractor(FIXED_SCOPE, SCEStrategy.class);
    // }
    //
    // public final void testEasySCE1() {
    // solver.options().setCoreGranularity(1);
    // testProofExtractor(EASY, SCEStrategy.class, EASY_MAX);
    // }
    //
    // public final void testMediumSCE1() {
    // solver.options().setCoreGranularity(1);
    // testProofExtractor(MEDIUM, SCEStrategy.class, MED_MAX);
    // }
    //
    // public final void testHardSCE1() {
    // solver.options().setCoreGranularity(1);
    // testProofExtractor(HARD, SCEStrategy.class, HARD_MAX);
    // }
    //
    // public final void testFixedSCE2() {
    // solver.options().setCoreGranularity(2);
    // testProofExtractor(FIXED_SCOPE, SCEStrategy.class);
    // }
    //
    // public final void testEasySCE2() {
    // solver.options().setCoreGranularity(2);
    // testProofExtractor(EASY, SCEStrategy.class, EASY_MAX);
    // }
    //
    // public final void testMediumSCE2() {
    // solver.options().setCoreGranularity(2);
    // testProofExtractor(MEDIUM, SCEStrategy.class, MED_MAX);
    // }
    //
    // public final void testHardSCE2() {
    // solver.options().setCoreGranularity(2);
    // testProofExtractor(HARD, SCEStrategy.class, HARD_MAX);
    // }
    //
    // public final void testFixedSCE3() {
    // solver.options().setCoreGranularity(3);
    // testProofExtractor(FIXED_SCOPE, SCEStrategy.class);
    // }
    //
    // public final void testEasySCE3() {
    // solver.options().setCoreGranularity(3);
    // testProofExtractor(EASY, SCEStrategy.class, EASY_MAX);
    // }
    //
    // public final void testMediumSCE3() {
    // solver.options().setCoreGranularity(3);
    // testProofExtractor(MEDIUM, SCEStrategy.class, MED_MAX);
    // }
    //
    // public final void testHardSCE3() {
    // solver.options().setCoreGranularity(3);
    // testProofExtractor(HARD, SCEStrategy.class, HARD_MAX);
    // }
    //
    // public final void testFixedRCE0() {
    // solver.options().setCoreGranularity(0);
    // testProofExtractor(FIXED_SCOPE, RCEStrategy.class);
    // }
    //
    // public final void testEasyRCE0() {
    // solver.options().setCoreGranularity(0);
    // testProofExtractor(EASY, RCEStrategy.class, EASY_MAX);
    // }
    //
    // public final void testMediumRCE0() {
    // solver.options().setCoreGranularity(0);
    // testProofExtractor(MEDIUM, RCEStrategy.class, MED_MAX);
    // }
    //
    // public final void testHardRCE0() {
    // solver.options().setCoreGranularity(0);
    // testProofExtractor(HARD, RCEStrategy.class, HARD_MAX);
    // }
    //
    // public final void testFixedRCE1() {
    // solver.options().setCoreGranularity(1);
    // testProofExtractor(FIXED_SCOPE, RCEStrategy.class);
    // }
    //
    // public final void testEasyRCE1() {
    // solver.options().setCoreGranularity(1);
    // testProofExtractor(EASY, RCEStrategy.class, EASY_MAX);
    // }
    //
    // public final void testMediumRCE1() {
    // solver.options().setCoreGranularity(1);
    // testProofExtractor(MEDIUM, RCEStrategy.class, MED_MAX);
    // }
    //
    // public final void testHardRCE1() {
    // solver.options().setCoreGranularity(1);
    // testProofExtractor(HARD, RCEStrategy.class, HARD_MAX);
    // }
    //
    // public final void testFixedRCE2() {
    // solver.options().setCoreGranularity(2);
    // testProofExtractor(FIXED_SCOPE, RCEStrategy.class);
    // }
    //
    // public final void testEasyRCE2() {
    // solver.options().setCoreGranularity(2);
    // testProofExtractor(EASY, RCEStrategy.class, EASY_MAX);
    // }
    //
    // public final void testMediumRCE2() {
    // solver.options().setCoreGranularity(2);
    // testProofExtractor(MEDIUM, RCEStrategy.class, MED_MAX);
    // }
    //
    // public final void testHardRCE2() {
    // solver.options().setCoreGranularity(2);
    // testProofExtractor(HARD, RCEStrategy.class, HARD_MAX);
    // }
    //
    // public final void testFixedRCE3() {
    // solver.options().setCoreGranularity(3);
    // testProofExtractor(FIXED_SCOPE, RCEStrategy.class);
    // }
    //
    // public final void testEasyRCE3() {
    // solver.options().setCoreGranularity(3);
    // testProofExtractor(EASY, RCEStrategy.class, EASY_MAX);
    // }
    //
    // public final void testMediumRCE3() {
    // solver.options().setCoreGranularity(3);
    // testProofExtractor(MEDIUM, RCEStrategy.class, MED_MAX);
    // }
    //
    // public final void testHardRCE3() {
    // solver.options().setCoreGranularity(3);
    // testProofExtractor(HARD, RCEStrategy.class, HARD_MAX);
    // }
    //
}
