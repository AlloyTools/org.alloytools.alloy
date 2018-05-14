package org.alloytools.alloy.classic.provider;

import org.alloytools.alloy.core.api.TSig;
import org.alloytools.alloy.solver.api.AlloySolution;
import org.alloytools.alloy.solver.api.IAtom;
import org.alloytools.alloy.solver.api.ITupleSet;

public class Atom implements IAtom {

    final Object        atom;
    final String        name;
    final String        prefix;
    final int           index;
    final TSig          sig;
    final AlloySolution solution;

    public Atom(AlloySolution solution, TSig sig, Object atom, String name) {
        this.solution = solution;
        this.atom = atom;
        this.sig = sig;
        this.name = name;
        String parts[] = name.split("\\$");
        this.prefix = parts[0];
        if (parts.length > 1 && parts[1].matches("\\d+")) {
            index = Integer.parseInt(parts[1]);
        } else {
            if (sig.getName().equals("Int")) {
                index = Integer.parseInt(name);
            } else {
                index = 0;
            }
        }
    }

    @Override
    public TSig getSig() {
        return sig;
    }

    @Override
    public Object getValue() {
        return atom;
    }

    @Override
    public String toString() {
        return name;
    }

    @Override
    public String getName() {
        return name;
    }


    @Override
    public int compareTo(IAtom o) {
        String a = sig.getName();
        String b = o.getSig().getName();
        int result = a.compareTo(b);
        if (result != 0)
            return result;

        result = Integer.compare(index, o.getIndex());
        if (result != 0)
            return result;

        return name.compareTo(o.getName());
    }

    @Override
    public ITupleSet asTupleSet() {
        return null;
    }

    @Override
    public int getIndex() {
        return index;
    }

    @Override
    public AlloySolution getSolution() {
        return solution;
    }

    @Override
    public int hashCode() {
        return atom.hashCode();
    }

    @Override
    public boolean equals(Object other) {
        if (this == other)
            return true;

        if (other.getClass() != getClass())
            return false;

        Atom o = (Atom) other;
        if (o.solution != solution) {
            return false;
        }

        return atom == o.atom;
    }


}
