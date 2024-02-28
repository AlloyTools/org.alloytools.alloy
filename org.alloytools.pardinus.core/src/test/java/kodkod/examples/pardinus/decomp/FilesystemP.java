/* 
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
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

public final class FilesystemP extends DModel {

	final private int n;
	final private Variant variant;

	private final Relation Obj, Name, File, Dir, Root, Cur, DirEntry;
	private final Relation entries, parent, name, contents;

	private final Universe u;
	
	public enum Variant {
		SAT,
		UNSAT;
	}

	public FilesystemP(String[] args) {
		this.n = Integer.valueOf(args[0]);
		this.variant = Variant.valueOf(args[1]);
		
		Obj = Relation.unary("Object");
		Name = Relation.unary("Name");
		File = Relation.unary("File");
		Dir = Relation.unary("Dir");
		Root = Relation.unary("Root");
		Cur = Relation.unary("Cur");
		DirEntry = Relation.unary("DirEntry");
		entries = Relation.binary("entries");
		parent = Relation.binary("parent");
		name = Relation.binary("name");
		contents = Relation.binary("contents");

		final List<String> atoms = new ArrayList<String>(n*3);
		for(int i = 0; i < n; i++)
			atoms.add("Object"+i);
		for(int i = 0; i < n; i++)
			atoms.add("Name"+i);
		for(int i = 0; i < n; i++)
			atoms.add("DirEntry"+i);
		
		u = new Universe(atoms);
		
	}

	@Override
	public PardinusBounds bounds1() {
		final TupleFactory f = u.factory();
		final PardinusBounds b = new PardinusBounds(u);
		
		final TupleSet ob = f.range(f.tuple("Object0"), f.tuple("Object"+(n-1)));
		final TupleSet nb = f.range(f.tuple("Name0"), f.tuple("Name"+(n-1)));
		final TupleSet eb = f.range(f.tuple("DirEntry0"), f.tuple("DirEntry"+(n-1)));		

		b.bound(Obj, ob);
		b.boundExactly(Root, f.setOf("Object0"));
		b.bound(Cur, ob);
		b.bound(File, ob);
		b.bound(Dir, ob);
		b.bound(Name, nb);
		b.bound(DirEntry, eb);
		
		b.bound(parent, ob.product(ob));
		b.bound(name, eb.product(nb));

		return b;
	}

	@Override
	public Bounds bounds2() {
		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);

		final TupleSet ob = f.range(f.tuple("Object0"), f.tuple("Object"+(n-1)));
		final TupleSet eb = f.range(f.tuple("DirEntry0"), f.tuple("DirEntry"+(n-1)));		

		b.bound(entries, ob.product(eb));
		b.bound(contents, eb.product(ob));
				
		return b;	
	}

	@Override
	public Formula partition1() {
		return decls1();
	}

	@Override
	public Formula partition2() {
		return variant==Variant.SAT?checkNoDirAliasesBuggy():checkNoDirAliasesCorrect();
	}

	private final Formula decls1() {
		// File and Dir partition object
		final Formula f0 = Obj.eq(File.union(Dir)).and(File.intersection(Dir).no());
		// Root and Cur are in Dir and do not intersect
		final Formula f11 = Root.in(Dir).and(Cur.in(Dir)).and(Root.intersection(Cur).no());
		// don't need to specify that Dir, Name, and DirEntry are disjoint; implied by bounds
		
//		one sig Root extends Dir {} { no parent }
		final Formula f61 = Root.join(parent).no();
		
		final Formula f31 = parent.partialFunction(Dir, Dir); 
		final Formula f41 = name.function(DirEntry, Name);
	
		final Variable dir = Variable.unary("this");
		final Formula f3 = dir.in(dir.join(parent.closure())).not();
		final Formula f4 = dir.eq(Root).not().implies(Root.in(dir.join(parent.closure())));
		final Formula f5 = f3.and(f4).forAll(dir.oneOf(Dir));

		final Variable d = Variable.unary("d");
		Formula xx = d.join(parent).one().forAll(d.oneOf(Dir.difference(Root)));
		
		return f0.and(f11).and(DirEntry.eq(DirEntry)).and(Name.eq(Name)).and(f61).and(f31).and(f41).and(f5).and(xx);
		

	}

	private final Formula decls2() {
		final Formula f2 = entries.in(Dir.product(DirEntry));
		final Formula f5 = contents.function(DirEntry, Obj);
		return f2.and(f5);
	}

	/**
	 * Returns all facts in the model.
	 * @return the facts.
	 */
	private final Formula facts() {
		// sig File extends Object {} { some d: Dir | this in d.entries.contents }
		final Variable file = Variable.unary("this");
		final Variable d = Variable.unary("d");
		final Formula f0 = file.in(d.join(entries).join(contents)).forSome(d.oneOf(Dir)).forAll(file.oneOf(File));
		
//		sig Dir extends Object {
//			  entries: set DirEntry,
//			  parent: lone Dir
//			} {
//			  parent = this.~@contents.~@entries
//			  all e1, e2 : entries | e1.name = e2.name => e1 = e2
//			  this !in this.^@parent
//			  this != Root => Root in this.^@parent
//			}
		
		final Variable dir = Variable.unary("this");
		final Variable e1 = Variable.unary("e1"), e2 = Variable.unary("e2");
		
		final Formula f1 = (dir.join(parent)).eq(dir.join(contents.transpose()).join(entries.transpose()));
		final Expression e0 = dir.join(entries);
		final Formula f2 = e1.join(name).eq(e2.join(name)).implies(e1.eq(e2)).forAll(e1.oneOf(e0).and(e2.oneOf(e0)));
		final Formula f5 = f1.and(f2).forAll(dir.oneOf(Dir));
		
//		sig DirEntry {
//			  name: Name,
//			  contents: Object
//			} { one this.~entries }

		final Variable entry = Variable.unary("this");
		final Formula f7 = entry.join(entries.transpose()).one().forAll(entry.oneOf(DirEntry));
		
		
		return f0.and(f5).and(f7);
	}

	
	private final Formula oneParentBuggy() { 
		//		fact OneParent {
		//	    // all directories besides root xhave one parent
		//	    all d: Dir - Root | one d.parent
		//	}
		return Formula.TRUE;
	}

	private final Formula oneParentCorrect() { 
		//		fact OneParent {
		//	    // all directories besides root xhave one parent
		//	    all d: Dir - Root | one d.parent
		//	}

		final Variable d = Variable.unary("d");
		return ((contents.join(d).one())).forAll(d.oneOf(Dir.difference(Root)));
	}

	
	/**
	 * Returns the no aliases assertion.
	 * @return the no aliases assertion.
	 */
	private final Formula noDirAliases() { 
		//all o: Dir | lone o.~contents
		final Variable o = Variable.unary("o");
		return o.join(contents.transpose()).lone().forAll(o.oneOf(Dir));
	}
	
	/**
	 * Returns the formula that 'checks' the noDirAliases assertion.
	 * @return decls() and facts() and noDirAliases().not()
	 */
	private final Formula checkNoDirAliasesCorrect() { 
		return decls2().and(facts()).and(oneParentCorrect()).and(noDirAliases().not());
	}

	/**
	 * Returns the formula that 'checks' the noDirAliases assertion.
	 * @return decls() and facts() and noDirAliases().not()
	 */
	private final Formula checkNoDirAliasesBuggy() { 
		return decls2().and(facts()).and(oneParentBuggy()).and(noDirAliases().not());
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
