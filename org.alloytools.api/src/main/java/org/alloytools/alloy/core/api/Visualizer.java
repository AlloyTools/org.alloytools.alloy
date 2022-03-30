package org.alloytools.alloy.core.api;

import java.net.URI;
import java.net.URISyntaxException;
import java.util.List;

/**
 * Represents a helper to visualize an instance.
 * <p>
 * Rendering can take place to different types. Types can be selected with
 * {@link Visualizer.Renderer}.
 */
public interface Visualizer {

    interface RenderType {

        Class< ? > getArgumentType();

        Class< ? > getOutputType();

        <A, O> Renderer<A,O> instantiate(Class<A> a, Class<O> o);

        default boolean matches(Class< ? > argument, Class< ? > output) {
            return argument.isAssignableFrom(getArgumentType()) && output.isAssignableFrom(getOutputType());
        }
    }

    /**
     * A preferred output format for a visualizer. Visualizer only has to support at
     * last one of these Hints.
     */
    interface Renderer<A, O> {

        default String mimeType() {
            return "text/plain;charset=utf8";
        }

        default String description() {
            return mimeType();
        }

        /**
         * Return a rendering according to the hint. If the hint was returned from
         * {@link #findRenderer} then the return object must be not null, otherwise it
         * may be null.
         *
         * @param instance the instance of a solution
         * @param options the options
         * @return a rendered object of the type specified by the hint
         */
        <T extends VisualizerOptions> O render(A instance, AlloyOptions< ? extends T> options);

        default O render(A instance) {
            return render(instance, newOptions());
        }

        default String extension() {
            return "";
        }

        <T extends VisualizerOptions> AlloyOptions<T> newOptions();

    }

    /**
     * The name of the visualizer
     *
     * @return the name
     */
    String getName();

    /**
     * The description of the visualizer. Used in tool tips etc.
     *
     * @return the description of the visualizer
     */
    String getDescription();

    /**
     * A URI to an icon that represents this visualizer
     *
     * @param pixels the number of horizontal/vertical pixels desired. This is a
     *            hint, a different size may be returned
     * @return an icon for the visualizer
     */
    default URI getIcon(int pixels) {
        try {
            return new URI("data:image/svg+xml;charset=utf-8;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIGNsYXNzPSJpY29uIiBhcmlhLWhpZGRlbj0idHJ1ZSIgZm9jdXNhYmxlPSJmYWxzZSIgdmlld0JveD0iMCAwIDUxMiA1MTIiPg0KICAgICAgPHBhdGggZmlsbD0iY3VycmVudENvbG9yIiBkPSJNMjU2IDhDMTE5IDggOCAxMTkgOCAyNTZzMTExIDI0OCAyNDggMjQ4IDI0OC0xMTEgMjQ4LTI0OFMzOTMgOCAyNTYgOHptMCA0NDhjLTExMC41IDAtMjAwLTg5LjUtMjAwLTIwMFMxNDUuNSA1NiAyNTYgNTZzMjAwIDg5LjUgMjAwIDIwMC04OS41IDIwMC0yMDAgMjAwem02MS44LTEwNC40bC04NC45LTYxLjdjLTMuMS0yLjMtNC45LTUuOS00LjktOS43VjExNmMwLTYuNiA1LjQtMTIgMTItMTJoMzJjNi42IDAgMTIgNS40IDEyIDEydjE0MS43bDY2LjggNDguNmM1LjQgMy45IDYuNSAxMS40IDIuNiAxNi44TDMzNC42IDM0OWMtMy45IDUuMy0xMS40IDYuNS0xNi44IDIuNnoiLz4NCiAgICA8L3N2Zz4=");
        } catch (URISyntaxException e) {
            throw new RuntimeException(e);
        }
    }

    List<RenderType> getRenderTypes();
}
