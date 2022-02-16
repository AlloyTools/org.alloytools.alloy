package org.alloytools.alloy.classic.provider;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

import org.alloytools.alloy.core.api.IAtom;
import org.alloytools.alloy.core.api.IRelation;
import org.alloytools.alloy.core.api.Solution;
import org.alloytools.alloy.core.api.TField;
import org.alloytools.alloy.core.api.TSignature;

import edu.mit.csail.sdg.ast.Sig;

public class Atom implements IAtom {

    final static AtomicInteger ID = new AtomicInteger(1000);

    final Object               atom;
    final String               name;
    final String               prefix;
    final int                  index;
    final TSignature           sig;
    final Solution             solution;
    final int                  id;
    final BasicType            type;

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

        type = getType(sig);
    }

    private BasicType getType(TSignature s) {
        if (s == Sig.SIGINT)
            return BasicType.NUMBER;
        if (s == Sig.STRING)
            return BasicType.STRING;

        List<TField> fields = new ArrayList<>(s.getFieldMap().values());
        if (fields.isEmpty()) {
            if (s == solution.bool())
                return BasicType.BOOLEAN;
            else
                return BasicType.IDENTIFIER;
        }
        return BasicType.OBJECT;
    }

    @Override
    public TSignature getSig() {
        return sig;
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
    public BasicType getBasicType() {
        return type;
    }

    @Override
    public int toInt() {
        if (type == BasicType.NUMBER)
            return index;
        else
            throw new IllegalArgumentException("Not an integer but a " + sig);
    }


    boolean toBool() {
        if (type == BasicType.BOOLEAN)
            return getName().equals("true");
        else
            throw new IllegalArgumentException("Not a boolean but a " + sig);
    }

    @Override
    public Object natural() {
        switch (getBasicType()) {
            case BOOLEAN :
                return toBool();
            case NUMBER :
                return toInt();
            case STRING :
                return toString();

            default :
            case IDENTIFIER :
            case OBJECT :
                return null;
        }
    }
}
