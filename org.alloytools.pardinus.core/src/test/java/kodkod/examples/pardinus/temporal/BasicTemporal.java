/**
 * 
 */
package kodkod.examples.pardinus.temporal;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

public class BasicTemporal {
	protected final Relation st1, st2, vr;
	
	public BasicTemporal() {
		st1 = Relation.unary("static1");
		st2 = Relation.unary("static2");
		vr = Relation.binary_variable("variable");
	}

	/**
	 * Returns the declarations.
	 * @return declarations
	 */
	public final Formula decls() {
		return Formula.and(st1.some(),st2.lone(),vr.in(st1.product(st2)).always());
	}
	
	/**
	 * Returns the conjunction of all  axioms.
	 * @return conjunction of all  axioms.
	 */
	public final Formula axioms() { 
		return Formula.and(vr.eq(vr.prime()).not().always(),st2.in(st1.join(vr)).always());
	}
	
	public final Formula check() {
		Variable x = Variable.unary("x");
		return Formula.and(decls(),axioms(),vr.some().not(),x.in(st1.join(vr)).not().after().forSome(x.oneOf(st2)));
	}

	/**
	 * Returns bounds for the given scope.
	 * @return bounds for the given scope.
	 */
	public final PardinusBounds bounds(int n) {
		assert n > 0;
		final List<String> atoms = new ArrayList<String>(n);
		for(int i = 0; i < n; i++)
			atoms.add("a"+i);
		final Universe u = new Universe(atoms);
		final PardinusBounds b = new PardinusBounds(u);
		final TupleFactory f = u.factory();
		final TupleSet s = f.allOf(1);
		b.bound(vr, s.product(s));
		b.bound(st1, s);
		b.bound(st2, s);
		return b;
	}
}
