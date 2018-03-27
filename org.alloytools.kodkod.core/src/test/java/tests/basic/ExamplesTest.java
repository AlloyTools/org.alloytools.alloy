package tests.basic;

import static kodkod.engine.Solution.Outcome.SATISFIABLE;
import static kodkod.engine.Solution.Outcome.TRIVIALLY_UNSATISFIABLE;
import static kodkod.engine.Solution.Outcome.UNSATISFIABLE;

import examples.alloy.AbstractWorldDefinitions;
import examples.alloy.CeilingsAndFloors;
import examples.alloy.Dijkstra;
import examples.alloy.FileSystem;
import examples.alloy.Handshake;
import examples.alloy.Hotel;
import examples.alloy.Lists;
import examples.alloy.Pigeonhole;
import examples.alloy.RingElection;
import examples.alloy.Toughnut;
import examples.alloy.Trees;
import examples.netconfig.Bigconfig;
import examples.tptp.ALG195;
import examples.tptp.ALG197;
import examples.tptp.ALG212;
import examples.tptp.COM008;
import examples.tptp.GEO091;
import examples.tptp.GEO092;
import examples.tptp.GEO115;
import examples.tptp.GEO158;
import examples.tptp.GEO159;
import examples.tptp.LAT258;
import examples.tptp.MED007;
import examples.tptp.MED009;
import examples.tptp.NUM374;
import examples.tptp.NUM378;
import examples.tptp.SET943;
import examples.tptp.SET948;
import examples.tptp.SET967;
import examples.tptp.TOP020;
import junit.framework.TestCase;
import kodkod.ast.Formula;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;

public class ExamplesTest extends TestCase {

    private final Solver solver;

    public ExamplesTest(String arg0) {
        super(arg0);
        this.solver = new Solver();
        this.solver.options().setSolver(SATFactory.MiniSat);
    }

    private Solution solve(Formula formula, Bounds bounds) {
        return solver.solve(formula, bounds);
    }

    private void check(String name, Solution sol, Solution.Outcome outcome, int primaryVars, int vars, int clauses) {
        assertEquals(outcome, sol.outcome());
        // System.out.println(Runtime.getRuntime().freeMemory() + "\t"
        // +sol.stats().translationTime() + "\t" + sol.stats().solvingTime() +
        // "\t" + sol.stats().primaryVariables() + "\t" +
        // sol.stats().variables() +"\t" + sol.stats().clauses() );
        // assertEquals(primaryVars, sol.stats().primaryVariables());
        // assertEquals(vars, sol.stats().variables());
        // assertEquals(clauses, sol.stats().clauses());
        // System.out.println(name+":"+sol.stats().primaryVariables()+":"+sol.stats().variables()+":"+sol.stats().clauses()+":"+sol.stats().translationTime()+":"+sol.stats().solvingTime());
    }

    /**
     * Runs the Bigconfig example for 1 hq, 9 subs, 4 unwindings.
     */
    public void testBigconfig() {
        final Bigconfig prob = new Bigconfig(4);
        final Solution sol = solve(prob.show(), prob.bounds(1, 9, 10));
        check(prob.getClass().getSimpleName(), sol, SATISFIABLE, 100, 2227, 4170);
    }

    /**
     * Runs the CeilingsAndFloors.checkBelowTooDoublePrime example for 6 Man, 6
     * Platform.
     */
    public void testCeilingsAndFloors_BelowTooDoublePrime() {
        final CeilingsAndFloors prob = new CeilingsAndFloors();
        final Solution sol = solve(prob.checkBelowTooDoublePrime(), prob.bounds(6, 6));
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 90, 1750, 3414);
    }

    /**
     * Runs the CeilingsAndFloors.checkBelowTooAssertion example for 6 Man, 6
     * Platform.
     */
    public void testCeilingsAndFloors_BelowTooAssertion() {
        final CeilingsAndFloors prob = new CeilingsAndFloors();
        final Solution sol = solve(prob.checkBelowTooAssertion(), prob.bounds(6, 6));
        check(prob.getClass().getSimpleName(), sol, SATISFIABLE, 90, 1750, 3414);
    }

    /**
     * Runs the Dijkstra example for 6 States, 6 Processes, and 6 Mutexes.
     */
    public void testDijkstra() {
        final Dijkstra prob = new Dijkstra();
        final Solution sol = solve(prob.checkDijkstraPreventsDeadlocks(), prob.bounds(6, 6, 6));
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 444, 4341, 18485);
    }

    /**
     * Runs FileSystem.checkNoDirAliases for 5.
     */
    public void testFileSystem() {
        final FileSystem prob = new FileSystem();
        final Solution sol = solve(prob.checkNoDirAliases(), prob.bounds(5));
        check(prob.getClass().getSimpleName(), sol, SATISFIABLE, 444, 4341, 18485);
    }

    /**
     * Runs Handshake.runPuzzle for 6.
     */
    public void testHandshake() {
        final Handshake prob = new Handshake();
        final Solution sol = solve(prob.runPuzzle(), prob.bounds(6));
        check(prob.getClass().getSimpleName(), sol, SATISFIABLE, 444, 4341, 18485);
    }

    /**
     * Runs Hotel.checkNoBadEntry for 4 and 6.
     */
    public void testHotel() {
        final Hotel prob = new Hotel();
        check(prob.getClass().getSimpleName(), solve(prob.checkNoBadEntry(), prob.bounds(4)), UNSATISFIABLE, 444, 4341, 18485);
        check(prob.getClass().getSimpleName(), solve(prob.checkNoBadEntry(), prob.bounds(6)), SATISFIABLE, 444, 4341, 18485);
    }

    /**
     * Runs Lists.runShow for 5.
     */
    public void testLists_runShow() {
        final Lists prob = new Lists();
        final Solution sol = solve(prob.runShow(), prob.bounds(5));
        check(prob.getClass().getSimpleName(), sol, SATISFIABLE, 444, 4341, 18485);
    }

    /**
     * Runs Lists.checkEmpties for 5.
     */
    public void testLists_checkEmpties() {
        final Lists prob = new Lists();
        final Solution sol = solve(prob.checkEmpties(), prob.bounds(5));
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 444, 4341, 18485);
    }

    /**
     * Runs Lists.checkReflexive for 5.
     */
    public void testLists_checkReflexive() {
        final Lists prob = new Lists();
        final Solution sol = solve(prob.checkReflexive(), prob.bounds(5));
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 444, 4341, 18485);
    }

    /**
     * Runs Lists.checkSymmetric for 5.
     */
    public void testLists_checkSymmetric() {
        final Lists prob = new Lists();
        final Solution sol = solve(prob.checkSymmetric(), prob.bounds(5));
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 444, 4341, 18485);
    }

    /**
     * Runs the Pigeonhole example for 10 Pigeons, 9 Holes.
     */
    public void testPigeonhole() {
        final Pigeonhole prob = new Pigeonhole();
        final Formula show = prob.declarations().and(prob.pigeonPerHole());
        final Solution sol = solve(show, prob.bounds(10, 9));
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 90, 1133, 2126);
    }

    /**
     * Runs RingElection.checkAtMostOneElected for 10 Times, 5 Processes.
     */
    public void testRingElection() {
        final RingElection prob = new RingElection();
        final Solution sol = solve(prob.checkAtMostOneElected(), prob.bounds(5, 10));
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 325, 8665, 29589);
    }

    /**
     * Runs Trees.checkEquivOfTreeDefns example for 4.
     */
    // TODO: see why this test fails when noOverflow is set to true!!!
    public void testTrees() {
        final Trees prob = new Trees();
        final Solution sol = solve(prob.checkEquivOfTreeDefns(), prob.bounds(4));
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 325, 8665, 29589);
    }

    /**
     * Runs the Toughnut example for an 8x8 board.
     */
    public void testToughnut() {
        final Toughnut prob = new Toughnut();
        final Solution sol = solve(prob.checkBelowTooDoublePrime(), prob.bounds(8));
        check(prob.getClass().getSimpleName(), sol, TRIVIALLY_UNSATISFIABLE, 0, 0, 0);
    }

    /**
     * Runs AbstractWorldDefinitions.checkA241 for 5.
     */
    public void testAWD_A241() {
        final AbstractWorldDefinitions prob = new AbstractWorldDefinitions();
        final Solution sol = solve(prob.checkA241(), prob.bounds(5));
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 407, 6968, 15413);
    }

    /**
     * Runs AbstractWorldDefinitions.checkAbOp_total for 5.
     */
    public void testAWD_AbOp_total() {
        final AbstractWorldDefinitions prob = new AbstractWorldDefinitions();
        final Solution sol = solve(prob.checkAbOp_total(), prob.bounds(5));
        check(prob.getClass().getSimpleName(), sol, TRIVIALLY_UNSATISFIABLE, 0, 0, 0);

    }

    /**
     * Runs AbstractWorldDefinitions.checkAbIgnore_inv for 5.
     */
    public void testAWD_AbIgnore_inv() {
        final AbstractWorldDefinitions prob = new AbstractWorldDefinitions();
        final Solution sol = solve(prob.checkAbIgnore_inv(), prob.bounds(5));
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 407, 6968, 15413);
    }

    /**
     * Runs AbstractWorldDefinitions.checkAbTransfer_inv for 5.
     */
    public void testAWD_AbTransfer_inv() {
        final AbstractWorldDefinitions prob = new AbstractWorldDefinitions();
        final Solution sol = solve(prob.checkAbTransfer_inv(), prob.bounds(5));
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 407, 6968, 15413);
    }

    /**
     * Runs ALG195.checkCO1.
     */
    public void testALG195() {
        final ALG195 prob = new ALG195();
        final Solution sol = solve(prob.checkCO1(), prob.bounds());
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 407, 6968, 15413);
    }

    /**
     * Runs ALG197.checkCO1.
     */
    public void testALG197() {
        final ALG197 prob = new ALG197();
        final Solution sol = solve(prob.checkCO1(), prob.bounds());
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 407, 6968, 15413);
    }

    /**
     * Runs ALG212.checkDistLong for 4.
     */
    public void testALG212() {
        final ALG212 prob = new ALG212();
        final Solution sol = solve(prob.checkDistLong(), prob.bounds(4));
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 407, 6968, 15413);
    }

    /**
     * Runs COM008.checkGoalToBeProved for 5.
     */
    public void testCOM008() {
        final COM008 prob = new COM008();
        final Solution sol = solve(prob.checkGoalToBeProved(), prob.bounds(5));
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 407, 6968, 15413);
    }

    /**
     * Runs GEO091.checkTheorem_2_13 for 6.
     */
    public void testGEO091() {
        final GEO091 prob = new GEO091();
        final Solution sol = solve(prob.checkTheorem_2_13(), prob.bounds(6));
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 407, 6968, 15413);
    }

    /**
     * Runs GEO092.checkProposition2141 for 6.
     */
    public void testGEO092() {
        final GEO092 prob = new GEO092();
        final Solution sol = solve(prob.checkProposition2141(), prob.bounds(6));
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 407, 6968, 15413);
    }

    /**
     * Runs GEO115.checkTheorem385 for 6.
     */
    public void testGEO115() {
        final GEO115 prob = new GEO115();
        final Solution sol = solve(prob.checkTheorem385(), prob.bounds(6));
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 407, 6968, 15413);
    }

    /**
     * Runs GEO158.checkConsistent for 6.
     */
    public void testGEO158() {
        final GEO158 prob = new GEO158();
        final Solution sol = solve(prob.checkConsistent(), prob.bounds(6));
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 407, 6968, 15413);
    }

    /**
     * Runs GEO159.checkDefs for 6.
     */
    public void testGEO159() {
        final GEO159 prob = new GEO159();
        final Solution sol = solve(prob.checkDefs(), prob.bounds(6));
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 407, 6968, 15413);
    }

    /**
     * Runs GRA019.checkGoalToBeProved for 6.
     */
    // public void testGRA019() {
    // final GRA013_026 prob = new GRA013_026();
    // final Solution sol = solve(prob.checkGoalToBeProved(), prob.bounds(6));
    // check(prob.getClass().getSimpleName(), sol, SATISFIABLE, 407, 6968,
    // 15413);
    // }

    /**
     * Runs LAT258.checkGoalToBeProved for 6.
     */
    public void testLAT258() {
        final LAT258 prob = new LAT258();
        final Solution sol = solve(prob.checkGoalToBeProved(), prob.bounds(6));
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 407, 6968, 15413);
    }

    /**
     * Runs MED007.checkTranssls2_qilt27 for 6.
     */
    public void testMED007() {
        final MED007 prob = new MED007();
        final Solution sol = solve(prob.checkTranssls2_qilt27(), prob.bounds(6));
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 407, 6968, 15413);
    }

    /**
     * Runs MED009.checkTranssls2_qige27 for 6.
     */
    public void testMED009() {
        final MED009 prob = new MED009();
        final Solution sol = solve(prob.checkTranssls2_qige27(), prob.bounds(6));
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 407, 6968, 15413);
    }

    /**
     * Runs NUM374.checkWilkie for 3.
     */
    public void testNUM374() {
        final NUM374 prob = new NUM374();
        final Solution sol = solve(prob.checkWilkie(), prob.bounds(3));
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 407, 6968, 15413);
    }

    /**
     * Runs NUM378.checkInequalities.
     */
    public void testNUM378() {
        final NUM378 prob = new NUM378();
        final Solution sol = solve(prob.checkInequalities(), prob.bounds());
        check(prob.getClass().getSimpleName(), sol, TRIVIALLY_UNSATISFIABLE, 0, 0, 0);
    }

    /**
     * Runs SET943.checkT96_zfmisc_1 for 3.
     */
    public void testSET943() {
        final SET943 prob = new SET943();
        final Solution sol = solve(prob.checkT96_zfmisc_1(), prob.bounds(3));
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 407, 6968, 15413);
    }

    /**
     * Runs SET948.checkT101_zfmisc_1 for 3.
     */
    public void testSET948() {
        final SET948 prob = new SET948();
        final Solution sol = solve(prob.checkT101_zfmisc_1(), prob.bounds(3));
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 407, 6968, 15413);
    }

    /**
     * Runs SET967.checkT120_zfmisc_1 for 3.
     */
    public void testSET967() {
        final SET967 prob = new SET967();
        final Solution sol = solve(prob.checkT120_zfmisc_1(), prob.bounds(3));
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 407, 6968, 15413);
    }

    /**
     * Runs TOP020.checkChallenge_AMR_1_4_4 for 6.
     */
    public void testTOP020() {
        final TOP020 prob = new TOP020();
        final Solution sol = solve(prob.checkChallenge_AMR_1_4_4(), prob.bounds(6));
        check(prob.getClass().getSimpleName(), sol, UNSATISFIABLE, 407, 6968, 15413);
    }
}
