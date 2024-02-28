
package kodkod.examples.pardinus.decomp;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IntConstant;
import kodkod.ast.IntExpression;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.decomp.DModel;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

public class RedBlackTreeP extends DModel {

	final private Relation Node, Root, left, right, parent, key, color, Black, Red, Num;
	final int n;
	final private Universe u;

	final private Variant1 v1;
	final private Variant2 v2;
	
	public enum Variant1 {
		COUNTER,
		THEOREM;
	}

	public enum Variant2 {
		V1,
		V2;
	}

	public RedBlackTreeP(String[] args) {
		Node = Relation.unary("Node");
		Black = Relation.unary("Black");
		Red = Relation.unary("Red");
		Root = Relation.unary("Root");
		left = Relation.binary("left");
		right = Relation.binary("right");
		parent = Relation.binary("parent");
		key = Relation.binary("key");
		color = Relation.binary("color");
		Num = Relation.unary("Num");
		
		n = Integer.valueOf(args[0]);
		v1 = RedBlackTreeP.Variant1.valueOf(args[1]);
		v2 = RedBlackTreeP.Variant2.valueOf(args[2]);
		
		final List<Object> atoms = new ArrayList<Object>(2*n+2);

		for (int i = 0; i < n; i++) 
			atoms.add("Node" + i);
		atoms.add("Red");
		atoms.add("Black");
		for (int i = 0; i < n; i++) 
			atoms.add(Integer.valueOf(i));
		
		u = new Universe(atoms);
	}

	private Formula decls1() {
		Formula f1 = Root.in(Node);
		Formula f2 = Root.one();
		Formula f3 = left.partialFunction(Node, Node);
		Formula f4 = right.partialFunction(Node, Node);
		
		Formula f5 = key.function(Node, Num);
		Variable i = Variable.unary("i");
		Formula f6 = key.join(i).lone().forAll(i.oneOf(Num));
		
		Formula res = Formula.and(f1,f2,f3,f4);
		if (v2 != Variant2.V2)
			res = Formula.and(res,f5,f6,ordered());
		return res;
	}
	
	private Formula ordered() {
		Expression children = (left.union(right)).closure().union(Expression.IDEN);

		Variable n = Variable.unary("n"),l = Variable.unary("l"),r = Variable.unary("r");
		Expression le = n.join(left).join(children);
		Expression re = n.join(right).join(children);
		Formula f1 = n.join(key).sum().gt(l.join(key).sum()).forAll(l.oneOf(le));
		Formula f2 = n.join(key).sum().lt(r.join(key).sum()).forAll(r.oneOf(re));
		return f1.and(f2).forAll(n.oneOf(Node));
	}
	
	@Override
	public Formula partition1() {
		Expression children = (left.union(right)).closure().union(Expression.IDEN);

		Variable n = Variable.unary("n");
		Formula acyclic3 = (left.union(right)).join(n).one().forAll(n.oneOf(Node.difference(Root)));
		Formula root3 = (left.union(right)).join(Root).no();
		Formula root4 = Root.in(Root.join((left.union(right)).closure())).not();
		Formula root6 = Root.join(children).eq(Node);
		Formula root5 = left.intersection(right).no();
		
		return Formula.and(decls1(),root3,root4,root5,root6,acyclic3);
	}

	private Formula decls2() {
		Formula f1 = color.function(Node, Black.union(Red));
		Formula f2 = parent.partialFunction(Node, Node);
		
		Formula f5 = key.function(Node, Num);
		Variable i = Variable.unary("i");
		Formula f6 = key.join(i).lone().forAll(i.oneOf(Num));
		
		if (v2 == Variant2.V2)
			return Formula.and(f1,f2,f5,f6,ordered());
		else
			return Formula.and(f1,f2);
	}
	
	private Formula color() {
		Expression children = (left.union(right)).closure().union(Expression.IDEN);
		Formula f1 = Root.join(color).eq(Black);
		Variable n = Variable.unary("n");
		Formula a1 = (n.join(color).eq(Red)).implies(n.join(left.union(right)).join(color).in(Black));
		Expression e21 = (n.join(left).join(children)).difference(color.join(Red));
		Expression e22 = (n.join(right).join(children)).difference(color.join(Red));
		Formula a2 = e21.count().eq(e22.count());
		Formula f2 = (a1.and(a2)).forAll(n.oneOf(Node));
		if (v1 == Variant1.THEOREM)
			return f1.and(f2).and(theorem().not());		
		else return f1.and(f2);
	}
	
	private Formula parent() {
		Variable n = Variable.unary("n");
		Formula f1 = n.join(parent).eq((left.union(right)).join(n)).forAll(n.oneOf(Node));
		return f1;
	}
	
	@Override
	public Formula partition2() {
		return decls2().and(color());
	}
	
	private Formula theorem() {
		
		Variable n1 = Variable.unary("n1");
		Variable n2 = Variable.unary("n2");
		Variable x = Variable.unary("x");
		Expression set = (x.join(left).no().or(x.join(right).no())).comprehension(x.oneOf(Node));
		IntExpression h1 = n1.join((left.union(right)).transpose().closure()).count();
		IntExpression h2 = n2.join((left.union(right)).transpose().closure()).count();
		
		Expression e1 = h1.minus(h2).toExpression();
		
		Formula f1 = e1.in(IntConstant.constant(0).toExpression().union(IntConstant.constant(-1).toExpression()).union(IntConstant.constant(1).toExpression()));
		return f1.forAll(n1.oneOf(set).and(n2.oneOf(set)));
	}

	@Override
	public PardinusBounds bounds1() {
		final TupleFactory f = u.factory();
		final PardinusBounds b = new PardinusBounds(u);
		
		final TupleSet nb = f.range(f.tuple("Node0"), f.tuple("Node"+(n-1)));
		final TupleSet kb = f.range(f.tuple(Integer.valueOf(0)), f.tuple(Integer.valueOf(n-1)));

		b.boundExactly(Node, nb);
		b.bound(Root, nb);
		b.bound(left, nb.product(nb));
		b.bound(right, nb.product(nb));
		b.boundExactly(Num, kb);

		if (v2 == Variant2.V1)
			b.bound(key, nb.product(kb));

		for (int i = 0; i < n; i++)
			b.boundExactly(i, f.setOf(Integer.valueOf(i)));
		
		return b;
	}

	@Override
	public Bounds bounds2() {
		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);

		final TupleSet nb = f.range(f.tuple("Node0"), f.tuple("Node"+(n-1)));
		final TupleSet cb = f.range(f.tuple("Red"), f.tuple("Black"));
		final TupleSet kb = f.range(f.tuple(Integer.valueOf(0)), f.tuple(Integer.valueOf(n-1)));

		if (v2 == Variant2.V2)
			b.bound(key, nb.product(kb));

		b.boundExactly(Black, f.setOf("Black"));
		b.boundExactly(Red, f.setOf("Red"));
		b.bound(color, nb.product(cb));
		b.bound(parent, nb.product(nb));

		return b;
	}
	


	private int bits(int n) {
		float x = (float) (Math.log(n*2) / Math.log(2));
		int y = (int) (1 + Math.floor(x));
		return Math.max(3, y);
	}
	
	private int maxInt() {
		return n;
	}
	

	@Override
	public int getBitwidth() {
		return bits(maxInt())+1;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder("RedBlackTree");
		sb.append(n);		
		return sb.toString();
	}

	@Override
	public String shortName() {
		return "RedBlackTree "+n+" "+v1.name()+" "+v2.name();
	}
}