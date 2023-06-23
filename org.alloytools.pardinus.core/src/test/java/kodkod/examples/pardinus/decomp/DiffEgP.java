package kodkod.examples.pardinus.decomp;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.decomp.DModel;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

public class DiffEgP extends DModel {

    private final Relation Subject, Resource, Action, Request, Conflicted;
    private final Relation sRequest, rRequest, action, sConflicted, rConflicted;
	
	private final Universe u;
	
	private int scope;
	
	/**
	 * Creates an instance of Dijkstra example.
	 */
	public DiffEgP(String[] args) {
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
		
		scope = Integer.valueOf(args[0]);

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
		
		u = new Universe(atoms);
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
		// a is a function from Request to Action
		final Formula f3 = action.function(Request, Action);
		// s is a function from Conflicted to Subject
		final Formula f4 = sConflicted.function(Conflicted, Subject);
		// r is a function from Conflicted to Resource
		final Formula f5 = rConflicted.function(Conflicted, Resource);
		return f3.and(f4).and(f5);
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


	@Override
	public PardinusBounds bounds1() {
		final TupleFactory f = u.factory();
		final PardinusBounds b = new PardinusBounds(u);
				
		final int max = scope - 1;
		
		final TupleSet sb = f.range(f.tuple("Subject0"), f.tuple("Subject"+max));
		final TupleSet rb = f.range(f.tuple("Resource0"), f.tuple("Resource"+max));
		final TupleSet qb = f.range(f.tuple("Request0"), f.tuple("Request"+max));

		
		b.bound(Subject, sb);
		b.bound(Resource, rb);
		b.bound(Request, qb);
		
		//sRequest, rRequest, action, sConflicted, rConflicted;
		b.bound(sRequest, qb.product(sb));
		b.bound(rRequest, qb.product(rb));
			
		return b;	}

	@Override
	public Bounds bounds2() {
		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);
		
		final int max = scope - 1;
		
		final TupleSet sb = f.range(f.tuple("Subject0"), f.tuple("Subject"+max));
		final TupleSet rb = f.range(f.tuple("Resource0"), f.tuple("Resource"+max));
		final TupleSet qb = f.range(f.tuple("Request0"), f.tuple("Request"+max));
		final TupleSet ab = f.range(f.tuple("Action0"), f.tuple("Action"+max));
		final TupleSet cb = f.range(f.tuple("Conflicted0"), f.tuple("Conflicted"+max));

		b.bound(Action, ab);
		b.bound(Conflicted, cb);
		
		//sRequest, rRequest, action, sConflicted, rConflicted;
		b.bound(action, qb.product(ab));
		b.bound(sConflicted, cb.product(sb));
		b.bound(rConflicted, cb.product(rb));
			
		return b;
	}

	@Override
	public Formula partition1() {
		final Formula f0 = Request.one(); // one Request
		// s is a function from Request to Subject
		final Formula f1 = sRequest.function(Request, Subject);
		// r is a function from Request to Resource
		final Formula f2 = rRequest.function(Request, Resource);

		return f0.and(f1).and(f2);
	}

	@Override
	public Formula partition2() {
		return runPol().and(decls());
	}

	@Override
	public int getBitwidth() {
		return 1;
	}
	@Override
	public String shortName() {
		// TODO Auto-generated method stub
		return null;
	}
}
