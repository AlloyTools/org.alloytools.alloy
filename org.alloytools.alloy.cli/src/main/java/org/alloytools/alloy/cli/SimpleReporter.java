package org.alloytools.alloy.cli;

import java.io.File;
import java.io.IOException;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import aQute.lib.env.Env;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.ast.Command;

class SimpleReporter extends A4Reporter {
    static Logger logger = LoggerFactory.getLogger("alloy");
	boolean db = true;

	static void db(String msg) {
		logger.info(msg);
	}

	Env cli;
	File output;

	public SimpleReporter(Env cli) throws IOException {
		this.cli = cli;
	}

	@Override
	public void debug(String msg) {
		cli.trace("%s",msg);
	}

	@Override
	public void parse(String msg) {
	}

	@Override
	public void typecheck(String msg) {
	}

	@Override
	public void warning(ErrorWarning msg) {
		cli.warning("%s %s", msg.pos, msg.msg);
	}

	@Override
	public void scope(String msg) {
	}

	@Override
	public void bound(String msg) {
	}

	@Override
	public void translate(String solver, int bitwidth, int maxseq, int mintrace, int maxtrace, int skolemDepth,
			int symmetry, String strat) {
		debug("Solver=" + solver + (maxtrace < 1 ? "" : " Steps=" + mintrace + ".." + maxtrace) + " Bitwidth="
				+ bitwidth + " MaxSeq=" + maxseq + " Symmetry=" + (symmetry > 0 ? ("" + symmetry) : "OFF") + " Mode="
				+ strat + "\n");
	}

	@Override
	public void solve(int step, int primaryVars, int totalVars, int clauses) {
		if (db)
			db("   " + totalVars + " vars. " + primaryVars + " primary vars. " + clauses + " clauses.\n");
	}

	@Override
	public void resultCNF(String filename) {
		cli.trace("received cnf file %s", filename);
		output = new File(filename);
	}

	@Override
	public void resultSAT(Object command, long solvingTime, Object solution) {
		if (db)
			db("   SAT!\n");
		if (!(command instanceof Command))
			return;
	}

	@Override
	public void resultUNSAT(Object command, long solvingTime, Object solution) {
		if (db)
			db("   UNSAT!\n");
	}
}
