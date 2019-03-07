package org.alloytools.kodkod.sat4j;

import java.util.Collections;
import java.util.Set;

import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.Solver;
import org.alloytools.alloy.core.spi.AlloySolverFactory;

public class SAT4JSolverFactory  implements AlloySolverFactory {

	@Override
	public Set<Solver> getAvailableSolvers(Alloy alloy) {
		
		return Collections.singleton( new SAT4JPlugin(alloy));
	}

}
