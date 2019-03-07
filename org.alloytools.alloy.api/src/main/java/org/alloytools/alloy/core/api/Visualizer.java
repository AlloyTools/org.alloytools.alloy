package org.alloytools.alloy.core.api;

import java.net.URI;

/**
 * Represents a helper to visualize an instance.
 * <p>
 * Rendering can take place to different types. Types can be selected with
 * {@link Visualizer.Hint}.
 */
public interface Visualizer {
	/**
	 * A preferrred output format for a visualizer. Visualizer only have to
	 * support at last one of these Hints.
	 */
	enum Hint {
	/**
	 * SVG Format
	 */
	SVG(String.class),
	/**
	 * HTML format
	 */
	HTML(String.class),
	/**
	 * Plain text. Will be displayed with a monospace font.
	 */
	TEXT(String.class),
	/**
	 * PNG format
	 */
	PNG(byte[].class),
	/**
	 * An interactive JComponent
	 */
	JCOMPONENT(Object.class);

		public final Class<?> type;

		Hint(Class<?> type) {
			this.type = type;
		}
	}

	/**
	 * The name of the visualizer
	 * 
	 * @return the name
	 */
	String getName();

	/**
	 * The description of the visualizer. Used in tooltips etc.
	 * 
	 * @return the description of the visualizer
	 */
	String getDescription();

	/**
	 * A URI to an icon that represents this visualizer
	 * 
	 * @param pixels the number of hor/vert pixels desired. This is a hint, a
	 *            different size may be returned
	 * @return an icon for the visualizer
	 */
	URI getIcon(int pixels);

	/**
	 * Negotiation to specify the output format.
	 * 
	 * @param hint the requested list of hints in preference order
	 * @return the first matching hint or null if not found
	 */
	Hint prefers(Hint... hint);

	/**
	 * Return a renderning according to the hint. If the hint was returned from
	 * {@link #prefers(Hint...)} then the return object must be not null,
	 * otherwise it may be null.
	 * 
	 * @param instance the instance of a solution
	 * @param hint the hint to define the format
	 * @return a rendered object of the type specified by the hint
	 */
	Object render(Instance instance, Hint hint);
}