package org.alloytools.alloy.solver.api;

import java.util.Set;

public interface ITupleSet extends Set<ITuple> {
	
    /**
     * Returns this.arity
     *
     * @return this.arity
     */
    public int arity();

    /**
     * Returns a tuple set that is the cross product of this and the specified set.
     *
     * @return {t: TupleSet | t.arity = this.arity + s.arity && t.universe =
     *         this.universe && t.tuples = this.tuples->s.tuples }
     */
    public ITupleSet product(ITupleSet s) ;

    /**
     * Returns a deep copy of this tuple set.
     *
     * @return {s: TupleSet - this | s.universe = this.universe && s.tuples =
     *         this.tuples }
     */

    public ITupleSet clone();

	public boolean isScalar();

	public IAtom scalar();

	public boolean isList();

	public ITuple get(int i);

	public ITupleSet head(int i);


	ITupleSet join( ITupleSet set);
	ITupleSet join( ITuple tuple);
	ITupleSet join( IAtom atom);
}
