package org.alloytools.alloy.classic.provider;

import org.alloytools.alloy.core.api.IRelation;
import org.alloytools.alloy.core.api.ITuple;
import org.alloytools.alloy.core.api.Solution;

abstract class Tuple implements ITuple {

    final Solution solution;

    public Tuple(Solution solution) {
        this.solution = solution;
    }

    @Override
    public int compareTo(ITuple o) {
        int arity = arity();
        int result = Integer.compare(arity, o.arity());
        if (result != 0)
            return result;

        for (int i = 0; i < arity; i++) {
            result = get(i).compareTo(o.get(i));
            if (result != 0) {
                return result;
            }
        }
        return 0;
    }

    @Override
    public IRelation asRelation() {
        return new Relation(solution, arity(), new Tuple[] {
                                                            this
        });
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        String del = "";
        for (int i = 0; i < arity(); i++) {
            sb.append(del);
            sb.append(get(i).getName());
            del = "->";
        }

        return sb.toString();
    }

    @Override
    public int hashCode() {
        int result = 1;
        int arity = arity();
        for (int i = 0; i < arity; i++) {
            Object element = get(i);
            result = 31 * result + element.hashCode();
        }

        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (this == other)
            return true;
        if ((other == null) || !(other instanceof ITuple))
            return false;

        ITuple it = (ITuple) other;
        int arity = this.arity();
        if (it.arity() != arity)
            return false;

        for (int i = 0; i < arity; i++) {
            if (get(i) != it.get(i))
                return false;
        }

        return true;
    }
}
