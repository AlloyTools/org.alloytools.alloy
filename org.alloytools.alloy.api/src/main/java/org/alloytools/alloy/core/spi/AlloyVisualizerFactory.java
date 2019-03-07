package org.alloytools.alloy.core.spi;

import java.util.Set;

import org.alloytools.alloy.core.api.Visualizer;

/**
 * A Service Loader factory to create instances of visualizers
 */
public interface AlloyVisualizerFactory {

	/**
	 * Get a list of visualizers
	 * 
	 * @return list of visualizers
	 */
	Set<Visualizer> getVisualizers();
}
