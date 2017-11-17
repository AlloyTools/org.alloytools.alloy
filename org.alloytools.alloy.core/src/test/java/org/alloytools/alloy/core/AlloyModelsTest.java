package org.alloytools.alloy.core;


import org.junit.Test;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

public class AlloyModelsTest {

	@Test
	public void testRecursion() throws Exception {
		String filename = "src/test/resources/test-recursion.als";
		Module world = CompUtil.parseEverything_fromFile(A4Reporter.NOP, null, filename);

		A4Options options = new A4Options();
		options.unrolls = 10;
		for (Command command : world.getAllCommands()) {
			A4Solution ans = TranslateAlloyToKodkod.execute_command(A4Reporter.NOP, world.getAllReachableSigs(),
					command, options);
			while (ans.satisfiable()) {
				String hc = "Answer: " + ans.toString().hashCode();
				System.out.println(hc);
				ans = ans.next();
			}
			return;
		}
	}
}
