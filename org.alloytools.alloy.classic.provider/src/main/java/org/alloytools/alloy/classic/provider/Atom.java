package org.alloytools.alloy.classic.provider;

import java.util.concurrent.atomic.AtomicInteger;

import org.alloytools.alloy.core.api.IAtom;
import org.alloytools.alloy.core.api.IRelation;
import org.alloytools.alloy.core.api.Solution;
import org.alloytools.alloy.core.api.TSignature;

public class Atom implements IAtom {

    final static AtomicInteger ID = new AtomicInteger(1000);

    final Object               atom;
    final String               name;
    final String               prefix;
    final int                  index;
    final TSignature           sig;
    final Solution             solution;
    final int                  id;

    public Atom(Solution solution, TSignature sig, Object atom, String name) {
        this.id = ID.getAndIncrement();
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
    public TSignature getSig() {
        return sig;
    }

    @Override
    public String toString() {
        return name + " [id=" + id + "]";
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
    public IRelation asTupleSet() {
        return null;
    }

    @Override
    public int getIndex() {
        return index;
    }

    @Override
    public Solution getSolution() {
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

    @Override
    public int toInt() {
        return Integer.parseInt(getName());
    }
}