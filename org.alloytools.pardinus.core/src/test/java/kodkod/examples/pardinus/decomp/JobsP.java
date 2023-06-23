package kodkod.examples.pardinus.decomp;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Formula;
import kodkod.ast.IntConstant;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.decomp.DModel;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

public class JobsP extends DModel {

	final private Relation Person, Job, Male, Female, HoldsJob, Husband, QualifiedJobs, Golfers, police, chef, roberta, nurse, actor, clerk, boxer, Pete;
	final private Universe u;

	
	public JobsP(String[] args) {
		Person = Relation.unary("Person");
		Job = Relation.unary("Job");
		Male = Relation.unary("Male");
		Female = Relation.unary("Female");
		HoldsJob = Relation.binary("HoldsJob");
		Husband = Relation.binary("Husband");
		QualifiedJobs = Relation.unary("QualifiedJobs");
		Golfers = Relation.unary("Golfers");

		roberta = Relation.unary("Roberta");
		chef = Relation.unary("chef");
		police = Relation.unary("police");
		boxer = Relation.unary("boxer");
		clerk = Relation.unary("clerk");
		nurse = Relation.unary("nurse");
		actor = Relation.unary("actor");
		Pete = Relation.unary("Pete");

		
		final List<Object> atoms = new ArrayList<Object>(12);
		atoms.add("Roberta");
		atoms.add("Thelma");
		atoms.add("Steve");
		atoms.add("Pete");
		atoms.add("chef");
		atoms.add("guard");
		atoms.add("clerk");
		atoms.add("police");
		atoms.add("teacher");
		atoms.add("nurse");
		atoms.add("actor");
		atoms.add("boxer");

		u = new Universe(atoms);
	}


	public Formula partition1() {
		final Formula f1 = HoldsJob.function(Job, Person);
		final Formula f2 = Husband.partialFunction(Female,Male);
		Variable x = Variable.unary("x"); 
		final Formula f3 = ((HoldsJob.join(x)).count()).eq(IntConstant.constant(2)).forAll(x.oneOf(Person));
		Variable y = Variable.unary("y");
		Variable z = Variable.unary("z");
		
		final Formula f4 = ((y.join(Husband).eq(z.join(Husband))).implies(y.eq(z))).forAll(y.oneOf(Female).and(z.oneOf(Female)));

		final Formula f5 = roberta.eq(roberta).and(chef.eq(chef)).and(police.eq(police));
		
		final Formula f6 = nurse.join(HoldsJob).in(Male);
		final Formula f7 = actor.join(HoldsJob).in(Male);
		final Formula f8 = (chef.join(HoldsJob).product(clerk.join(HoldsJob))).in(Husband);
		final Formula f9 = roberta.in(boxer.join(HoldsJob)).not();
		final Formula f10 = HoldsJob.join(Pete).in(QualifiedJobs).not();
		
		final Formula f11 = QualifiedJobs.in(Job);
		
		Formula res = Formula.and(f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,f11);

		return res;
	}

	public Formula partition2() {
		final Formula f1 = Golfers.count().eq(IntConstant.constant(3));
		final Formula f2 = Golfers.eq(roberta.union(chef.join(HoldsJob)).union(police.join(HoldsJob)));

		Formula res = Formula.and(f1,f2);
		return res;
	}

	/**
	 * Returns a bounds for the given number of persons.
	 * 
	 * @return a bounds for the given number of persons.
	 */
	public PardinusBounds bounds1() {
		final TupleFactory f = u.factory();
		final PardinusBounds b = new PardinusBounds(u);
		
		final TupleSet pb = f.range(f.tuple("Roberta"), f.tuple("Pete"));
		final TupleSet jb = f.range(f.tuple("chef"), f.tuple("boxer"));
		final TupleSet fb = f.range(f.tuple("Roberta"), f.tuple("Thelma"));
		final TupleSet mb = f.range(f.tuple("Steve"), f.tuple("Pete"));
		final TupleSet qb = f.range(f.tuple("police"), f.tuple("nurse"));
		
		b.boundExactly(Person, pb);
		b.boundExactly(Job, jb);
		b.boundExactly(Female, fb);
		b.boundExactly(Male, mb);
		b.boundExactly(QualifiedJobs, qb);
		b.boundExactly(roberta, f.setOf("Roberta"));
		b.boundExactly(police, f.setOf("police"));
		b.boundExactly(chef, f.setOf("chef"));
		b.boundExactly(boxer, f.setOf("boxer"));
		b.boundExactly(Pete, f.setOf("Pete"));
		b.boundExactly(actor, f.setOf("actor"));
		b.boundExactly(clerk, f.setOf("clerk"));
		b.boundExactly(nurse, f.setOf("nurse"));

		b.bound(HoldsJob, jb.product(pb));
		b.bound(Husband, fb.product(mb));
		
		return b;
	}

	public Bounds bounds2() {
		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);
		final TupleSet pb = f.range(f.tuple("Roberta"), f.tuple("Pete"));
		b.bound(Golfers, pb);
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
		return 3;
	}
	

	public String toString() {
		StringBuilder sb = new StringBuilder("Jobs");
		return sb.toString();
	}


	@Override
	public String shortName() {
		// TODO Auto-generated method stub
		return null;
	}
}
