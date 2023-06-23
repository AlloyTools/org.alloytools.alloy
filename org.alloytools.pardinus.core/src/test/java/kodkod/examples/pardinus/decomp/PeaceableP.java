
package kodkod.examples.pardinus.decomp;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.decomp.DModel;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

public class PeaceableP extends DModel {

	final private Relation BQueens, WQueens, wrow, brow, wcol, bcol, Num;
	final private Universe u;
	final private int n, d;

	public PeaceableP(String[] args) {
		WQueens = Relation.unary("WQueens");
		BQueens = Relation.unary("BQueens");
		wrow = Relation.binary("wrow");
		brow = Relation.binary("brow");
		wcol = Relation.binary("wcol");
		bcol = Relation.binary("bcol");
		Num = Relation.unary("Num");

		n = Integer.valueOf(args[0]);
		d = Integer.valueOf(args[1]);

		final List<Object> atoms = new ArrayList<Object>(2*n+2*d);
		for (int i = 0; i < n; i++) 
			atoms.add("BQueen" + i);
		for (int i = 0; i < n; i++) 
			atoms.add("WQueen" + i);
		for (int i = 0; i < (2*d)-1; i++)
			atoms.add(Integer.valueOf(i));
		u = new Universe(atoms);
	}
	
	private Formula noThreat() {
		Variable bq = Variable.unary("bq");
		Variable wq = Variable.unary("wq");
		Formula f1 = bq.join(brow).eq(wq.join(wrow)).not();
		Formula f2 = bq.join(bcol).eq(wq.join(wcol)).not();
		Formula f3 = bq.join(brow).sum().plus(bq.join(bcol).sum()).eq(wq.join(wcol).sum().plus(wq.join(wrow).sum())).not();
		Formula f4 = bq.join(brow).sum().plus(wq.join(wcol).sum()).eq(bq.join(bcol).sum().plus(wq.join(wrow).sum())).not();
		return Formula.and(f1,f2,f3,f4).forAll(bq.oneOf(BQueens).and(wq.oneOf(WQueens)));
	}
	
	private Formula declsW() {
		Formula f3 = wrow.function(WQueens, Num);
		Formula f4 = wcol.function(WQueens, Num);
		return Formula.and(f3,f4);
	}
	
	private Formula declsB() {
		Formula f1 = brow.function(BQueens, Num);
		Formula f2 = bcol.function(BQueens, Num);
		return Formula.and(f1,f2);
	}
	
	private Formula allDiffB() {
		Variable bq1 = Variable.unary("bq1");
		Variable bq2 = Variable.unary("bq2");
		Formula f1 = (bq1.eq(bq2).or(bq1.join(bcol).eq(bq2.join(bcol)).not().or(bq1.join(brow).eq(bq2.join(brow)).not())));
		Formula f2 = f1.forAll(bq1.oneOf(BQueens).and(bq2.oneOf(BQueens)));
		return f2;
	}
	
	private Formula allDiffW() {
		Variable wq1 = Variable.unary("wq1");
		Variable wq2 = Variable.unary("wq2");
		Formula f3 = (wq1.eq(wq2).or(wq1.join(wcol).eq(wq2.join(wcol)).not().or(wq1.join(wrow).eq(wq2.join(wrow)).not())));
		Formula f4 = f3.forAll(wq1.oneOf(WQueens).and(wq2.oneOf(WQueens)));
		return f4;
	}
	
	public Formula partition1() {
		return Formula.and(declsB(), allDiffB());
	}

	public Formula partition2() {
		return Formula.and(declsW(), noThreat(), allDiffW());
	}

	/**
	 * Returns a bounds for the given number of persons.
	 * 
	 * @return a bounds for the given number of persons.
	 */
	public PardinusBounds bounds1() {
		final TupleFactory f = u.factory();
		final PardinusBounds b = new PardinusBounds(u);
		
		final TupleSet bb = f.range(f.tuple("BQueen0"), f.tuple("BQueen"+(n-1)));
		final TupleSet ib = f.range(f.tuple(0), f.tuple((d-1)));

		b.boundExactly(BQueens, bb);
		b.bound(bcol, bb.product(ib));
		b.bound(brow, bb.product(ib));
		b.boundExactly(Num, ib);
		
		for (int i = 0; i<2*d-1; i++)
			b.boundExactly(i, f.setOf(Integer.valueOf(i)));

		
		return b;
	}

	public Bounds bounds2() {
		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);
		
		final TupleSet wb = f.range(f.tuple("WQueen0"), f.tuple("WQueen"+(n-1)));
		final TupleSet ib = f.range(f.tuple(0), f.tuple((d-1)));

		b.boundExactly(WQueens, wb);
		b.bound(wcol, wb.product(ib));
		b.bound(wrow, wb.product(ib));

		return b;
	}

	@Override
	public int getBitwidth() {
		return bits(maxInt())+1;
	}
	
	
	private int bits(int n) {
		float x = (float) (Math.log(n*2) / Math.log(2));
		int y = (int) (1 + Math.floor(x));
		return Math.max(3, y);
	}
	
	private int maxInt() {
		return 2*d;
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder("Peaceable");
		sb.append(d);
		sb.append("-");
		sb.append(n);		
		return sb.toString();
	}

	@Override
	public String shortName() {
		// TODO Auto-generated method stub
		return null;
	}
}