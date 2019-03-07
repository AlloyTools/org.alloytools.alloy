package org.alloytools.alloy.classic.provider;

import org.alloytools.alloy.core.api.Module;

import edu.mit.csail.sdg.parser.CompModule;

public interface AlloyModuleClassic extends Module {

	CompModule getOriginalModule();

}
