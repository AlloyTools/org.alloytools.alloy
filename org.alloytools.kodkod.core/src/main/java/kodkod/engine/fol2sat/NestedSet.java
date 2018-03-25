package kodkod.engine.fol2sat;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

/**
 * Implements a data structure that contains sets of values at different nesting
 * levels.
 *
 * @author aleks
 */
@SuppressWarnings("unchecked" )
public class NestedSet<T> implements Iterable<T> {

    private final NestedSet<T> parent;
    private final Set<T>       elems;

    private NestedSet(NestedSet<T> parent) {
        this(parent, new HashSet<T>());
    }

    private NestedSet(NestedSet<T> parent, Set<T> elems) {
        this.parent = parent;
        this.elems = elems;
    }

    public NestedSet<T> createNested() {
        return new NestedSet<T>(this);
    }

    public void add(T elem) {
        this.elems.add(elem);
    }

    public void addAll(Collection< ? extends T> elems) {
        this.elems.addAll(elems);
    }

    public NestedSet<T> parent() {
        return parent;
    }

    @Override
    public Iterator<T> iterator() {
        return elems.iterator();
    }

    @SuppressWarnings("rawtypes" )
    private static final NestedSet EMPTY = new NestedSet(null);

    public static <T> NestedSet<T> empty() {
        return EMPTY;
    }

}
