package org.alloytools.alloy.classic.solver;

import java.util.Map;

import org.allotools.conversion.util.DTOs;
import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.AlloyModule;
import org.alloytools.alloy.core.api.TCommand;
import org.alloytools.alloy.solver.api.AlloyOptions;
import org.alloytools.alloy.solver.api.AlloySolver;

public abstract class AbstractSolver implements AlloySolver {

	private final Alloy core;

	public AbstractSolver(Alloy core) {
		this.core = core;
	}


	public Alloy getAlloy() {
		return core;
	}

	public String toString() {
		return getName();
	}
	
	protected AlloyOptions processOptions(AlloyModule module, TCommand command, AlloyOptions optionsOrNull) {
		
		AlloyOptions options = optionsOrNull == null ? DTOs.dflt(getOptionsType()) : optionsOrNull;
		
        assert getOptionsType().isAssignableFrom(options.getClass()) : options.getClass() + " is invalid option class for " + this;

		Map<String, String> sourceOptions = module.getSourceOptions(command);		
		DTOs.set(options,sourceOptions);
		
		return options;
	}

	
}
