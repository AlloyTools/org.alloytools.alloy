package examples.alloy;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.Universe;

/*
-- A simple access control policy framework

sig Subject {}
sig Resource {} 
sig Action {}
one sig Request {s : Subject,  r : Resource, a : Action }

-- predicates from policies
sig Conflicted {s : Subject, r : Resource}

-- An access rule
pred RevPaperNoConflict (req : Request) {
  no conf : Conflicted | req.s in conf.s && req.r in conf.r 
}

-- A Policy (would normally be disjunction of rules)
pred pol (req: Request) {
  RevPaperNoConflict(req)
}

run pol for 2
*/
public final class DiffEg {
//	 sigs

    private final Relation Subject, Resource, Action, Request, Conflicted;
    private final Relation sRequest, rRequest, action, sConflicted, rConflicted;

	public DiffEg() {
		Subject = Relation.unary("Subject");
		Resource = Relation.unary("Resource");
		Action = Relation.unary("Action");
		Request = Relation.unary("Request");
		Conflicted = Relation.unary("Conflicted");
		sRequest = Relation.binary("s");
		rRequest = Relation.binary("r");
		action = Relation.binary("a");
		sConflicted = Relation.binary("s");
		rConflicted = Relation.binary("r");
	}

	/**
	 * Returns the formulas implicit in the declarations.
	 * @return formulas implicit in:
	 * <pre>
	 * sig Subject {}
	 * sig Resource {} 
	 * sig Action {}
	 * one sig Request {s : Subject,  r : Resource, a : Action }
	 * sig Conflicted {s : Subject, r : Resource}
	 * </pre>
	 */
	public final Formula decls() {
		final Formula f0 = Request.one(); // one Request
		// s is a function from Request to Subject
		final Formula f1 = sRequest.function(Request, Subject);
		// r is a function from Request to Resource
		final Formula f2 = rRequest.function(Request, Resource);
		// a is a function from Request to Action
		final Formula f3 = action.function(Request, Action);
		// s is a function from Conflicted to Subject
		final Formula f4 = sConflicted.function(Conflicted, Subject);
		// r is a function from Conflicted to Resource
		final Formula f5 = rConflicted.function(Conflicted, Resource);
		return f0.and(f1).and(f2).and(f3).and(f4).and(f5);
	}
	
	/**
	 * Returns the RevPaperNoConflict access rule.
	 * @return
	 * <pre>
	 * pred RevPaperNoConflict (req : Request) {
	 *  no conf : Conflicted | req.s in conf.s && req.r in conf.r 
	 * }
	 * </pre>
	 */
	public final Formula revPaperNoConflict(Expression req) {
		final Variable conf = Variable.unary("conf");
		// req.s in conf.s  
		final Formula f0 = req.join(sRequest).in(conf.join(sConflicted));
		// req.r in conf.r 
		final Formula f1 = req.join(rRequest).in(conf.join(rConflicted));
		// (no conf : Conflicted | req.s in conf.s && req.r in conf.r) <=>
		// all conf : Conflicted | !(req.s in conf.s && req.r in conf.r)		
		return (f0.and(f1)).not().forAll(conf.oneOf(Conflicted));
	}
	
	/**
	 * Returns the pol predicate
	 * @return 
	 * <pre>
	 * pred pol (req: Request) {
	 *  RevPaperNoConflict(req)
	 * }
	 * </pre>
	 */
	public final Formula pol(Expression req) {
		return revPaperNoConflict(req);
	}
	
	/**
	 * Returns a formula that 'runs' the pol predicate.
	 * @return 
	 * <pre>
	 * some req: Request | pol(req)
	 * </pre>
	 */
	public final Formula runPol() {
		final Variable req = Variable.unary("req");
		return pol(req).forSome(req.oneOf(Request));
	}

	/**
	 * Returns the bounds for the given alloy scope.
	 * @return bounds for the given alloy scope
	 */
	public final Bounds bounds(int scope) {
		assert scope > 0;
		final List<String> atoms = new ArrayList<String>(4*scope + 1);
		// Subject, Resource, Action, Conflicted
		for(int i = 0; i < scope; i++)
			atoms.add("Subject"+i);
		for(int i = 0; i < scope; i++)
			atoms.add("Resource"+i);
		for(int i = 0; i < scope; i++)
			atoms.add("Action"+i);
		for(int i = 0; i < scope; i++)
			atoms.add("Conflicted"+i);
		for(int i = 0; i < scope; i++)
			atoms.add("Request"+i);
		
		final Universe u = new Universe(atoms);
		final TupleFactory f = u.factory();
		final Bounds b =  new Bounds(u);
		
		final int max = scope - 1;
		
		b.bound(Subject, f.range(f.tuple("Subject0"), f.tuple("Subject"+max)));
		b.bound(Resource, f.range(f.tuple("Resource0"), f.tuple("Resource"+max)));
		b.bound(Action, f.range(f.tuple("Action0"), f.tuple("Action"+max)));
		b.bound(Conflicted, f.range(f.tuple("Conflicted0"), f.tuple("Conflicted"+max)));
		b.bound(Request, f.range(f.tuple("Request0"), f.tuple("Request"+max)));
		
		//sRequest, rRequest, action, sConflicted, rConflicted;
		b.bound(sRequest, b.upperBound(Request).product(b.upperBound(Subject)));
		b.bound(rRequest, b.upperBound(Request).product(b.upperBound(Resource)));
		b.bound(action, b.upperBound(Request).product(b.upperBound(Action)));
		b.bound(sConflicted, b.upperBound(Conflicted).product(b.upperBound(Subject)));
		b.bound(rConflicted, b.upperBound(Conflicted).product(b.upperBound(Resource)));
		return b;
	}
	
	
	private static void usage() {
		System.out.println("java examples.DiffEq [scope]");
		System.exit(1);
	}
	
	/**
	 * Usage: java examples.DiffEq [scope]
	 */
	public static void main(String[] args) {
		if (args.length < 1)
			usage();
		
		try {
			final int n = Integer.parseInt(args[0]);
			if (n < 1)
				usage();
			final DiffEg model = new DiffEg();
			final Solver solver = new Solver();
			
			final Formula f = model.runPol();
			final Bounds b = model.bounds(n);
			
			System.out.println(f);
			
			final Solution sol = solver.solve(f, b);
			System.out.println(sol);
			
		} catch (NumberFormatException nfe) {
			usage();
		}
	}
}
