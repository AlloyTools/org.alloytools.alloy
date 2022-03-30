package org.alloytools.alloy.classic.provider;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import org.alloytools.alloy.core.api.IAtom;
import org.alloytools.alloy.core.api.IRelation;
import org.alloytools.alloy.core.api.ITuple;
import org.alloytools.alloy.core.api.Solution;

import aQute.lib.collections.ExtList;

public class Relation implements IRelation {

    final Solution solution;
    final int      arity;
    final Tuple[]  tuples;

    Relation(Solution solution, int arity, Tuple[] tuples) {
        this.solution = solution;
        this.tuples = tuples;
        this.arity = tuples.length == 0 ? 0 : arity;
        assert asSet().size() == tuples.length;
    }

    public Relation(Solution solution, int arity, List< ? extends IAtom> atoms) {
        this(solution, arity, toTuples(solution, arity, atoms));
    }

    public Relation(Solution solution, int arity, Collection< ? extends ITuple> tuples) {
        this(solution, arity, tuples.toArray(new Tuple[tuples.size()]));
    }

    public Relation(Solution s) {
        this(s, 0, new Tuple[0]);
    }

    public Relation(Solution s, IAtom atom) {

        this(s, 1, new Tuple[] {
                                new Tuple(s) {

                                    @Override
                                    public int arity() {
                                        return 1;
                                    }

                                    @Override
                                    public IAtom get(int n) {
                                        if (n != 0)
                                            throw new IllegalArgumentException("Invalid index for a tuple");
                                        return atom;
                                    }
                                }
        });
    }

    @Override
    public int arity() {
        return arity;
    }

    @Override
    public IRelation join(IRelation right) {
        assert solution == right.getSolution();

        if (this.arity == 0 || right.arity() == 0)
            return solution.none();

        int arity = this.arity() + right.arity() - 2;
        if (arity == 0)
            return solution.none();

        List<IAtom> atoms = new ArrayList<>();

        for (ITuple l : this) {
            IAtom last = l.last();

            for (ITuple r : right) {
                IAtom first = r.first();

                if (last == first) {
                    for (int i = 0; i < l.arity() - 1; i++) {
                        atoms.add(l.get(i));
                    }

                    for (int i = 1; i < r.arity(); i++) {
                        atoms.add(r.get(i));
                    }
                }
            }
        }

        return solution.create(arity, atoms);
    }

    @Override
    public IRelation product(IRelation right) {
        assert solution == right.getSolution();

        List<IAtom> atoms = new ArrayList<>();
        int arity = this.arity() + right.arity();
        if (arity == 0)
            return solution.none();

        for (ITuple l : this) {
            for (ITuple r : right) {
                for (int i = 0; i < l.arity(); i++) {
                    atoms.add(l.get(i));
                }
                for (int i = 0; i < r.arity(); i++) {
                    atoms.add(r.get(i));
                }
            }
        }
        return solution.create(arity, atoms);
    }

    @Override
    public boolean isNone() {
        return solution.none() == this;
    }

    @Override
    public IRelation head() {
        return split(0, 1);
    }

    private IRelation split(int from, int to) {
        if (this.isEmpty())
            return solution.none();

        assert from >= 0;
        assert from < to;
        assert to > from;
        assert to <= arity;

        int arity = to - from;

        TreeSet<Tuple> tuples = new TreeSet<>();
        for (ITuple tuple : this) {
            List<IAtom> atoms = new ArrayList<>();
            for (int i = from; i < to; i++)
                atoms.add(tuple.get(i));
            Tuple t = new Tuple(solution) {

                @Override
                public int arity() {
                    return arity;
                }

                @Override
                public IAtom get(int n) {
                    // TODO Auto-generated method stub
                    return atoms.get(n);
                }
            };
            tuples.add(t);
        }
        if (tuples.size() == 0)
            return solution.none();

        return new Relation(solution, arity, tuples);
    }

    @Override
    public IRelation tail() {
        return split(1, arity);
    }

    @Override
    public Iterator<ITuple> iterator() {
        return new ExtList<ITuple>(tuples).iterator();
    }

    @Override
    public int size() {
        return tuples.length;
    }

    @Override
    public Solution getSolution() {
        return solution;
    }

    static Tuple[] toTuples(Solution solution, int arity, List< ? extends IAtom> atoms) {
        Set<Tuple> removeDuplicates = new HashSet<>();
        for (int i = 0; i < atoms.size(); i += arity) {
            int base = i;
            Tuple tuple = new Tuple(solution) {

                @Override
                public int arity() {
                    return arity;
                }

                @Override
                public IAtom get(int i) {
                    return atoms.get(base + i);
                }
            };
            removeDuplicates.add(tuple);
        }
        Tuple[] result = removeDuplicates.toArray(new Tuple[removeDuplicates.size()]);
        Arrays.sort(result);
        return result;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append("{ ");

        String del = "";
        for (ITuple tuple : tuples) {
            sb.append(del);
            sb.append(tuple);
            del = ", ";
        }

        sb.append(" }");
        return sb.toString();
    }

    /**
     * Return a relation that takes the first column of the this as the first and
     * second column. Further columns are ignored.
     *
     * @return a new relation
     */
    public IRelation toIdent() {

        List<IAtom> atoms = new ArrayList<>();
        for (ITuple t : this) {
            atoms.add(t.first());
            atoms.add(t.first());
        }
        return solution.create(2, atoms);
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + arity;
        result = prime * result + Arrays.hashCode(tuples);
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if ((obj == null) || (getClass() != obj.getClass()))
            return false;
        Relation other = (Relation) obj;
        if (arity == 0 && other.arity == 0)
            return true;
        if ((arity != other.arity) || !Arrays.equals(tuples, other.tuples))
            return false;
        return true;
    }

    @Override
    public boolean in(IRelation other) {
        if (this.isEmpty())
            return true;

        if (other.isEmpty() || wrongArity(other))
            return false;

        for (Tuple t : tuples) {
            if (!other.contains(t))
                return false;
        }
        return true;
    }

    @Override
    public boolean contains(ITuple t) {
        if (this.isEmpty())
            return false;
        for (Tuple tuple : tuples) {
            if (tuple.equals(t))
                return true;
        }
        return false;
    }

    @Override
    public IRelation difference(IRelation other) {
        if (other.isEmpty())
            return this;

        if (wrongArity(other))
            return solution.none();

        SortedSet<ITuple> a = asSet();
        a.removeAll(other.asSet());
        return new Relation(solution, arity, a);
    }

    @Override
    public IRelation union(IRelation other) {
        if (wrongArity(other))
            return solution.none();

        if (this.isEmpty())
            return other;
        if (other.isEmpty())
            return this;

        SortedSet<ITuple> a = asSet();
        a.addAll(other.asSet());
        return new Relation(solution, arity, a);
    }

    @Override
    public IRelation intersection(IRelation other) {
        if (wrongArity(other) || this.isEmpty() || other.isEmpty())
            return solution.none();

        SortedSet<ITuple> a = asSet();
        a.retainAll(other.asSet());
        return new Relation(solution, arity, a);
    }

    private boolean wrongArity(IRelation other) {
        return arity != 0 && other.arity() != 0 && arity != other.arity();
    }

    @Override
    public SortedSet<ITuple> asSet() {
        return new TreeSet<>(Arrays.asList(tuples));
    }


    @Override
    public IRelation select(IAtom right) {
        IRelation r = new Relation(solution, right);
        return r.join(this);
    }

    @Override
    public boolean isTrue() {
        return scalar().map(IAtom::toBool).orElseThrow(() -> new IllegalArgumentException("can only coerce a boolean realtion to a boolean"));
    }

    @Override
    public boolean isError() {
        return solution.error() == this;
    }

    @Override
    public int compareTo(IRelation o) {
        int compare = Integer.compare(arity, o.arity());
        if (compare == 0) {
            compare = Integer.compare(size(), o.size());
        }
        if (compare == 0) {
            for (int i = 0; i < size(); i++) {
                Tuple a = this.tuples[i];
                ITuple b = o.getTuple(i);
                compare = a.compareTo(b);
                if (compare != 0)
                    break;
            }
        }
        return compare;
    }

    @Override
    public ITuple getTuple(int i) {
        return tuples[i];
    }

}
