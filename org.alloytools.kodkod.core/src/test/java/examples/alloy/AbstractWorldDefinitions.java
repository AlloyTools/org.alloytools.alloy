package examples.alloy;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.LinkedList;
import java.util.List;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.ConsoleReporter;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.Universe;

/**
 * KK encoding of mondex/a.als together with mondex/common.als.
 * 
 * @author Emina Torlak
 */
public final class AbstractWorldDefinitions {
	// relations declared in common.als
	private final Relation Coin, Purse, TransferDetails;
	private final Relation from, to, value;

	// relations declared in a.als
	private final Relation AbWorld, AbPurse, aNullIn, AIN, AOUT, aNullOut;
	private final Relation abAuthPurse, abBalance, abLost;
	
	/**
	 * Constructs an instance of AbstractWorldDefinitions.
	 */
	public AbstractWorldDefinitions() {
		Coin = Relation.unary("Coin");
		Purse = Relation.unary("Purse");
		TransferDetails = Relation.unary("TransferDetails");
		from = Relation.binary("from");
		to = Relation.binary("to");
		value = Relation.binary("value");
		
		AbWorld = Relation.unary("AbWorld");
		AbPurse = Relation.unary("AbPurse");
		aNullIn = Relation.unary("aNullIn");
		AIN = Relation.unary("AIN");
		AOUT = Relation.unary("AOUT");
		aNullOut = Relation.unary("aNullOut");
		abAuthPurse = Relation.binary("abAuthPurse");
		abBalance = Relation.ternary("abBalance");
		abLost  = Relation.ternary("abLost");
	}
	
	/**
	 * Returns the declaration constraints for mondex/common.als
	 * @return declaration constraints for mondex/common.als
	 */
	public Formula decls() {
		
		final Formula f0 = from.function(TransferDetails, Purse);
		final Formula f1 = to.function(TransferDetails, Purse);
		final Formula f2 = value.in(TransferDetails.product(Coin));
		
		final Formula f3 = AbPurse.in(Purse);
		final Formula f4 = abAuthPurse.in(AbWorld.product(AbPurse));
		final Formula f5 = abBalance.in(AbPurse.product(Coin).product(AbWorld));
		final Formula f6 = abLost.in(AbPurse.product(Coin).product(AbWorld));
		final Formula f7 = AIN.in(aNullIn.union(TransferDetails));
		final Formula f8 = aNullOut.in(AOUT);
		
//		final List<Formula> fs = Arrays.asList(f0, f1, f2, f3, f4, f5, f6, f7, f8);
//		Collections.shuffle(fs);
		
		return Formula.and(f0, f1, f2, f3, f4, f5, f6, f7, f8);//Formula.and(fs);
		
	}
	
	/**
	 * Applies the XiTransfer predicate to the arguments.
	 * @return application of the XiTransfer predicate to the arguments.
	 */
	public final Formula XiTransfer(Expression p, Expression pprime) {
		final Formula f0 = p.join(from).eq(pprime.join(from));
		final Formula f1 = p.join(to).eq(pprime.join(to));
		final Formula f2 = p.join(value).eq(pprime.join(value));
		return Formula.and(f0, f1, f2);
	}
	
	/**
	 * Returns the application of the Abstract predicate.
	 * @return application of the Abstract predicate.
	 */
	public Formula Abstract(Expression s) {
		final Expression e0 = s.join(abAuthPurse).join(abBalance).join(s).intersection(s.join(abAuthPurse).join(abLost).join(s));
		final Formula f0 = e0.no();
		
		final Expression e1 = s.join(abAuthPurse).product(Expression.UNIV);
		final Expression e2 = e1.intersection((abBalance.union(abLost)).join(s));
		final Formula f1 = e2.in(AbPurse.product(Coin));
		final Variable c = Variable.unary("c");
		final Formula f2 = e2.join(c).lone().forAll(c.oneOf(Coin));
		
		return Formula.and(f0, f1, f2);
	}
	/**
	 * Returns the application of the XiAbPurse predicate.
	 * @return application of the XiAbPurse predicate.
	 */
	public Formula XiAbPurse(Expression s, Expression sprime, Expression a) {
		final Expression aRestrict = a.product(Expression.UNIV);
		final Formula f0 = aRestrict.intersection(abBalance.join(s)).eq(aRestrict.intersection(abBalance.join(sprime)));
		final Formula f1 = aRestrict.intersection(abLost.join(s)).eq(aRestrict.intersection(abLost.join(sprime)));
		return f0.and(f1);
	}
	/**
	 * Returns the application of the totalBalance function.
	 * @return application of the totalBalance function.
	 */
	public Expression totalBalance(Expression s) {
		return s.join(abAuthPurse).join(abBalance).join(s);
	}
	
	/**
	 * Returns the application of the totalLost function.
	 * @return application of the totalLost function.
	 */
	public Expression totalLost(Expression s) {
		return s.join(abAuthPurse).join(abLost).join(s);
	}
	
	/**
	 * Returns the application of the NoValueCreation predicate.
	 * @return application of the NoValueCreation predicate.
	 */
	public Formula NoValueCreation(Expression s, Expression sprime) {
		return totalBalance(sprime).in(totalBalance(s));
	}
	
	/**
	 * Returns the application of the AllValueAccounted predicate.
	 * @return application of the AllValueAccounted predicate.
	 */
	public Formula AllValueAccounted(Expression s, Expression sprime) {
		return totalBalance(sprime).union(totalLost(sprime)).in(totalBalance(s).union(totalLost(s)));
	}

	/**
	 * Returns the application of the Authentic predicate.
	 * @return application of the Authentic predicate.
	 */
	public Formula Authentic(Expression s, Expression p) {
		return p.in(s.join(abAuthPurse));
	}
	
	/**
	 * Returns the application of the Authentic predicate.
	 * @return application of the Authentic predicate.
	 */
	public Formula SufficientFundsProperty(Expression s, Expression t) {
		return t.join(value).in(t.join(from).join(abBalance).join(s));
	}
	
	/**
	 * Returns the application of the AbOp predicate.
	 * @return application of the AbOp predicate.
	 */
	public Formula AbOp(Expression a_out) {
		return a_out.eq(aNullOut);
	}
	
	/**
	 * Returns the application of the AbIgnore predicate.
	 * @return application of the AbIgnore predicate.
	 */
	public Formula AbIgnore(Expression s, Expression sprime, Expression a_out) {
		final Formula f0 = AbOp(a_out);
		final Formula f1 = s.join(abAuthPurse).eq(sprime.join(abAuthPurse));
		final Formula f2 = XiAbPurse(s, sprime, s.join(abAuthPurse));
		return f0.and(f1).and(f2);
	}
	
	
	/**
	 * Returns the application of the AbWorldSecureOp predicate.
	 * @return application of the AbWorldSecureOp predicate.
	 */
	public Formula AbWorldSecureOp(Expression s, Expression sprime, Expression a_in, Expression a_out) {
		final Formula f0 = AbOp(a_out);
		final Formula f1 = a_in.in(TransferDetails);

		final Expression e0 = a_in.join(from);
		final Expression e1 = a_in.join(to);
		final Expression e2 = s.join(abAuthPurse).difference(e0).difference(e1);
		final Expression e3 = sprime.join(abAuthPurse).difference(e0).difference(e1);
		final Formula f2 = e2.eq(e3);
		
		final Formula f3 = XiAbPurse(s, sprime, e2);
		
		return Formula.and(f0, f1, f2, f3);
	}
		
	/**
	 * Returns the application of the AbTransferOkay predicate.
	 * @return application of the AbTransferOkay predicate.
	 */
	public Formula AbTransferOkay(Expression s, Expression sprime, Expression a_in, Expression a_out) {
		final Expression e0 = a_in.join(from);
		final Expression e1 = a_in.join(to);
		
		final Formula f0 = AbWorldSecureOp(s, sprime, a_in, a_out);
		final Formula f1 = Authentic(s, e0);
		final Formula f2 = Authentic(s, e1);
		final Formula f3 = SufficientFundsProperty(s, a_in);
		final Formula f4 = e0.intersection(e1).no();
		
		final Formula f5 = e0.join(abBalance).join(sprime).eq(e0.join(abBalance).join(s).difference(a_in.join(value)));
		final Formula f6 = e0.join(abLost).join(sprime).eq(e0.join(abLost).join(s));
		final Formula f7 = e1.join(abBalance).join(sprime).eq(e1.join(abBalance).join(s).union(a_in.join(value)));
		final Formula f8 = e1.join(abLost).join(sprime).eq(e1.join(abLost).join(s));
		
		final Formula f9 = Authentic(sprime, e0);
		final Formula f10 = Authentic(sprime, e1);
		
		return Formula.and(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10);
		
	}

	/**
	 * Returns the application of the AbTransferLost predicate.
	 * @return application of the AbTransferOkay predicate.
	 */
	public Formula AbTransferLost(Expression s, Expression sprime, Expression a_in, Expression a_out) {
		final Expression e0 = a_in.join(from);
		final Expression e1 = a_in.join(to);
		
		final Formula f0 = AbWorldSecureOp(s, sprime, a_in, a_out);
		final Formula f1 = Authentic(s, e0);
		final Formula f2 = Authentic(s, e1);
		final Formula f3 = SufficientFundsProperty(s, a_in);
		final Formula f4 = e0.intersection(e1).no();
		
		final Formula f5 = e0.join(abBalance).join(sprime).eq(e0.join(abBalance).join(s).difference(a_in.join(value)));
		final Formula f6 = e0.join(abLost).join(sprime).eq(e0.join(abLost).join(s).union(a_in.join(value)));
		
		final Formula f7 = XiAbPurse(s, sprime, e1);
				
		final Formula f8 = Authentic(sprime, e0);
		final Formula f9 = Authentic(sprime, e1);
		
		return Formula.and(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9);
	}
	
	/**
	 * Returns the application of the AbTransfer predicate.
	 * @return application of the AbTransfer predicate.
	 */
	public Formula AbTransfer(Expression s, Expression sprime, Expression a_in, Expression a_out) {
		return AbTransferOkay(s, sprime, a_in, a_out).or(AbTransferLost(s, sprime, a_in, a_out)).
			or(AbIgnore(s, sprime, a_out));
	}
	
	/**
	 * Returns decls() && !A241()
	 * @return  decls() && !A241()
	 */
	public Formula checkA241() { 
		return decls().and(A241().not());
	}
	
	/**
	 * Returns decls() && !AbOp_total()
	 * @return  decls() && !AbOp_total()
	 */
	public Formula checkAbOp_total() { 
		return decls().and(AbOp_total().not());
	}
	
	/**
	 * Returns decls() && !AbIgnore_inv()
	 * @return  decls() && !AbIgnore_inv()
	 */
	public Formula checkAbIgnore_inv() { 
		return decls().and(AbIgnore_inv().not());
	}
	
	/**
	 * Returns decls() && !AbTransfer_inv()
	 * @return  decls() && !AbTransfer_inv()
	 */
	public Formula checkAbTransfer_inv() { 
		return decls().and(AbTransfer_inv().not());
	}
	
	/**
	 * Returns the A241 assertion.
	 * @return A241 assertion
	 */
	public Formula A241() {
		final Variable s = Variable.unary("s");
		final Variable sprime = Variable.unary("s'");
		final Variable a_in = Variable.unary("a_in");
		final Variable a_out = Variable.unary("a_out");
		
		final Formula f0 = Abstract(s).and(Abstract(sprime)).and(AbTransfer(s, sprime, a_in, a_out));
		final Formula f1 = NoValueCreation(s, sprime).and(AllValueAccounted(s, sprime));
		final Formula f2 = f0.implies(f1).
			forAll(s.oneOf(AbWorld).and(sprime.oneOf(AbWorld)).and(a_in.oneOf(AIN)).and(a_out.oneOf(AOUT)));
		
		return f2;
	}
	
	/**
	 * Returns the AbOp_total assertion.
	 * @return AbOp_total assertion
	 */
	public Formula AbOp_total() {
		final Variable a = Variable.unary("a");
		final Variable a_in = Variable.unary("a_in");
		
		final Formula f0 = Abstract(a).implies(AbIgnore(a, a, aNullOut).and(AbTransfer(a, a, a_in, aNullOut)));
		final Formula f1 = f0.forAll(a.oneOf(AbWorld).and(a_in.oneOf(AIN)));
		
		return f1;
	}
	
	
	/**
	 * Returns the AbIgnore_inv assertion.
	 * @return AbIgnore_inv assertion
	 */
	public Formula AbIgnore_inv() {
		final Variable a = Variable.unary("a");
		final Variable aprime = Variable.unary("a'");
		final Variable a_out = Variable.unary("a_out");
		
		final Formula f0 = (Abstract(a).and(AbIgnore(a, aprime, a_out))).implies(Abstract(aprime));
		final Formula f1 = f0.forAll(a.oneOf(AbWorld).and(aprime.oneOf(AbWorld)).and(a_out.oneOf(AOUT)));
		
		return f1;
	}
	
	
	/**
	 * Returns the AbTransfer_inv assertion.
	 * @return AbTransfer_inv assertion
	 */
	public Formula AbTransfer_inv() {
		final Variable a = Variable.unary("a");
		final Variable aprime = Variable.unary("a'");
		final Variable a_in = Variable.unary("a_in");
		final Variable a_out = Variable.unary("a_out");
		
		final Formula f0 = (Abstract(a).and(AbTransfer(a, aprime, a_in, a_out))).implies(Abstract(aprime));
		final Formula f1 = f0.
			forAll(a.oneOf(AbWorld).and(aprime.oneOf(AbWorld)).and(a_in.oneOf(AIN)).and(a_out.oneOf(AOUT)));
		
		return f1;
	}
	
	/**
	 * Returns the bounds for the given scope.
	 * @return bounds for the given scope
	 */
	public final Bounds bounds(int scope) {
		final List<String> atoms = new LinkedList<String>();
		
		final int max = scope-1;
		for(int i = 0; i < scope; i++) { atoms.add("Coin"+i); }
		for(int i = 0; i < scope; i++) { atoms.add("Purse"+i);}
		for(int i = 0; i < scope; i++) { atoms.add("TransferDetails"+i);}
		atoms.add("aNullIn");
		for(int i = 0; i < scope; i++) { atoms.add("AbWorld"+i);}
		for(int i = 0; i < max; i++) { atoms.add("AOUT"+i);}
		atoms.add("aNullOut");
		
		final Universe u = new Universe(atoms);
		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);
		
		
		b.bound(Coin, f.range(f.tuple("Coin0"), f.tuple("Coin"+max)));
		b.bound(Purse, f.range(f.tuple("Purse0"), f.tuple("Purse"+max)));
		b.bound(TransferDetails, f.range(f.tuple("TransferDetails0"), f.tuple("TransferDetails"+max)));
		b.bound(AbWorld, f.range(f.tuple("AbWorld0"), f.tuple("AbWorld"+max)));
		b.bound(AbPurse, b.upperBound(Purse));
		b.bound(AOUT, f.range(f.tuple("AOUT0"), f.tuple("aNullOut")));
		b.bound(AIN, f.range(f.tuple("TransferDetails0"), f.tuple("aNullIn")));
		
		b.boundExactly(aNullIn, f.setOf("aNullIn"));
		b.boundExactly(aNullOut, f.setOf("aNullOut"));
					
		b.bound(from, b.upperBound(TransferDetails).product(b.upperBound(Purse)));
		b.bound(to, b.upperBound(TransferDetails).product(b.upperBound(Purse)));
		b.bound(value, b.upperBound(TransferDetails).product(b.upperBound(Coin)));
		b.bound(abAuthPurse, b.upperBound(AbWorld).product(b.upperBound(AbPurse)));
		
		b.bound(abBalance, b.upperBound(AbPurse).product(b.upperBound(Coin)).product(b.upperBound(AbWorld)));
		b.bound(abLost, b.upperBound(AbPurse).product(b.upperBound(Coin)).product(b.upperBound(AbWorld)));
		
		return b;
	}
	
	private static void usage() {
		System.out.println("java examples.AbstractWorldDefinitions [A241 | AbOp_total | AbIgnore_inv | AbTransfer_inv] [univ size]");
		System.exit(1);
	}
	
	/**
	 * Usage: java examples.AbstractWorldDefinitions [A241 | AbOp_total | AbIgnore_inv | AbTransfer_inv] [univ size]
	 */
	public static void main(String[] args) {
		if (args.length < 2)
			usage();
		
		try {
			final String assertion = args[0];
			final int n = Integer.parseInt(args[1]);
			if (n < 1)
				usage();
			final AbstractWorldDefinitions model = new AbstractWorldDefinitions();
			final Solver solver = new Solver();
			solver.options().setSolver(SATFactory.MiniSat);
			solver.options().setReporter(new ConsoleReporter());
//			solver.options().setFlatten(true);
			final Method method = model.getClass().getMethod(assertion);
			final Formula f = model.decls().and(((Formula)method.invoke(model)).not());
			final Bounds b = model.bounds(n);
			System.out.println(f);
			final Solution sol = solver.solve(f, b);
			System.out.println(sol);
		} catch (NumberFormatException nfe) {
			usage();
		} catch (SecurityException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (NoSuchMethodException e) {
			usage();
		} catch (IllegalArgumentException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IllegalAccessException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (InvocationTargetException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

}
