/* 
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 * Pardinus -- Copyright (c) 2013-present, Nuno Macedo, INESC TEC
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package kodkod.examples.pardinus.decomp;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.ConstantExpression;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.NaryExpression;
import kodkod.ast.Relation;
import kodkod.ast.operator.ExprOperator;
import kodkod.engine.decomp.DModel;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 * An example decomposed model for testing whether the symmetries are being
 * correctly calculated for decomposed problems. Considers variants whose
 * partial or integrated problems become trivial.
 * 
 * @see kodkod.test.pardinus.decomp.SymmetryTests
 * 
 * @author Nuno Macedo // [HASLab] decomposed, symbolic model finding
 *
 */
public final class SymmetryS extends DModel {

	final private int n, m;

	private final Relation r, s;
	private final Relation b1,b2,b3,a1,a2,a3;
	private final Universe u;

	public enum VariantBounds {
		V1, V2, V3, V4, V5, V6, V7, V8, V9, V0;
	}

	public enum VariantFormulas {
		V1, V2, V3, V4;
	}

	public enum VariantOrder {
		V1, V2, V3, V4;
	}

	VariantBounds v1;
	VariantFormulas v2;
	VariantOrder v3;

	public SymmetryS(String[] args) {
		this.n = Integer.valueOf(args[0]);
		this.m = n;
		this.v1 = VariantBounds.valueOf(args[1]);
		this.v2 = VariantFormulas.valueOf(args[2]);
		this.v3 = VariantOrder.valueOf(args[3]);

		r = Relation.unary("r");
		s = Relation.unary("s");

		a1 = Relation.binary("a_next");
		a2 = Relation.unary("a_first");
		a3 = Relation.unary("a_last");

		b1 = Relation.binary("b_next");
		b2 = Relation.unary("b_first");
		b3 = Relation.unary("b_last");

		final List<String> atoms = new ArrayList<String>(2 * n);
		for (int i = 0; i < m; i++)
			atoms.add("A" + i);

		u = new Universe(atoms);
	}

	@Override
	public PardinusBounds bounds1() {
		final TupleFactory f = u.factory();
		final PardinusBounds bnd = new PardinusBounds(u);

		TupleSet upper_r = f.range(f.tuple("A0"), f.tuple("A" + (m - 1)));
		TupleSet lower_r = f.noneOf(1);

		if (v1 == VariantBounds.V3 || v1 == VariantBounds.V4
				|| v1 == VariantBounds.V5)
			lower_r.add(f.tuple("A0"));

		if (v1 == VariantBounds.V5 || v1 == VariantBounds.V6)
			lower_r.add(f.tuple("A" + (m - 1)));

		if (v1 == VariantBounds.V7)
			lower_r = upper_r;

		if (v1 == VariantBounds.V9)
			upper_r = lower_r;

		bnd.bound(r, lower_r, upper_r);

		if (v3 == VariantOrder.V2 || v3 == VariantOrder.V3) {
			bnd.bound(a1, upper_r.product(upper_r));
			bnd.bound(a2, upper_r);
			bnd.bound(a3, upper_r);
		}
		
		return bnd;
	}

	@Override
	public Bounds bounds2() {
		final TupleFactory f = u.factory();
		final PardinusBounds bnd = new PardinusBounds(u);

		Expression upper_b = r;
		Expression lower_b = ConstantExpression.NONE;

		Expression[] a = new Expression[m];
		for (int i = 0; i < m; i ++)
			a[i] = bnd.reify(f.setOf(f.tuple("A"+i)));
		
		if (v1 == VariantBounds.V2 || v1 == VariantBounds.V5)
			lower_b.union(a[0]);

		if (v1 == VariantBounds.V6)
			lower_b.union(NaryExpression.compose(ExprOperator.UNION, a));

		if (v1 == VariantBounds.V8)
			lower_b = upper_b;
		
		if (v1 == VariantBounds.V0)
			upper_b = lower_b;

		bnd.bound(s, lower_b, upper_b);

		if (v3 == VariantOrder.V3 || v3 == VariantOrder.V4) {
			bnd.bound(b1, upper_b.product(upper_b));
			bnd.bound(b2, upper_b);
			bnd.bound(b3, upper_b);
		}
		
		return bnd;
	}

	@Override
	public Formula partition1() {
		Formula x15 = r.one();

		Formula x12 = x15;
		Formula f = (v2 == VariantFormulas.V1 || v2 == VariantFormulas.V2) ? x12
				: Formula.TRUE;
		
		return f.and(v3 == VariantOrder.V2 || v3 == VariantOrder.V3?a1.totalOrder(r, a2, a3).and(a2.in(a1.join(r))):Formula.TRUE);
	}

	@Override
	public Formula partition2() {
		Formula x14 = s.one();

		Formula f2 = x14;
		Formula f = (v2 == VariantFormulas.V2 || v2 == VariantFormulas.V3) ? f2
				: Formula.TRUE;
		
		return f.and(v3 == VariantOrder.V3 || v3 == VariantOrder.V4?b1.totalOrder(s, b2, b3).and(b2.in(b1.join(s))):Formula.TRUE);
	}

	@Override
	public int getBitwidth() {
		return 1;
	}

	@Override
	public String shortName() {
		return "Symmetry " + n;
	}

}
