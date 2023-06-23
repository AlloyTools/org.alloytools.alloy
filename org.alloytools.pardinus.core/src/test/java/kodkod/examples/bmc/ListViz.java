/* 
 * Kodkod -- Copyright (c) 2005-2012, Emina Torlak
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
package kodkod.examples.bmc;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import kodkod.ast.Expression;
import kodkod.ast.Relation;
import kodkod.engine.Evaluator;
import kodkod.instance.Instance;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.util.nodes.PrettyPrinter;

/**
 * @author Emina Torlak
 *
 */
class ListViz {
	
	static enum State { PRE, POST }
	
	static final void printStateGraph(String name, ListEncoding enc, Instance inst, State state) {
		if (inst == null) return;
		final String prop = System.getProperty("kodkod.examples.bmc.out");
		if (prop!=null) {
			PrintStream pos = null;
			final String path = prop+"/"+name;
			try {
				pos = new PrintStream(path+".dot");
				printStateGraph(pos, enc, inst, state);	
			} catch (FileNotFoundException e) {
			} finally {
				if (pos != null) {
					pos.close();
					final String dot = System.getProperty("kodkod.examples.bmc.dot");
					if (dot != null) {
						try {
							Runtime.getRuntime().exec(new String[]{dot, "-Tpdf", "-o" + path + ".pdf" , path + ".dot"});
							final String viewer = System.getProperty("demo.viewer");
							if (viewer != null)
								Runtime.getRuntime().exec(new String[] {"open", "-a", viewer, path+".pdf"});
						} catch (IOException e) {}
					}
				}
			}
		}
	}
	
	private static final void printStateGraph(PrintStream stream, ListEncoding enc, Instance inst, 
			State state) {
		
		final Evaluator eval = new Evaluator(inst);
		
		final Expression thisList = enc.thisList, data = enc.data, head,  next;
		if (state==State.PRE) {
			head = enc.head;
			next = enc.next;
		} else {
			head = enc.head0();
			next = enc.next3();
		}
		
		stream.append("digraph {\n");
		stream.append("bgcolor=transparent;\n");
		stream.append("margin=0;\n");
		stream.append("rankdir=" + (state==State.PRE ? "LR" : "RL") + ";\n");
		stream.append("edge [fontname=\"Arial\",fontsize=18, arrowsize=.75, penwidth=.75]\n");
		stream.append("node [shape=box, fontname=\"Arial\", fontsize=18, penwidth=.75 ];");

		final Object thisListAtom = eval.evaluate(thisList).iterator().next().atom(0);
		final java.util.List<Object> nodes = sort(eval.evaluate(next.closure()));
		final boolean nilConnected = nodes.remove("nil");
		final Map<Object, Object> dataMap = functionToMap(eval.evaluate(data));
		
		final Map<Object, String> id = new LinkedHashMap<Object, String>();
		id.put(thisListAtom, "this");
		id.put("nil", "null");
		for(Object node : nodes) { 
			id.put(node, node.toString());
		}
		for(Tuple t : eval.evaluate(enc.string)) { 
			id.put(t.atom(0), t.atom(0).toString());
		}
		
		printNode(stream, thisListAtom, "this");
		stream.append("node [shape=ellipse, style=filled, fillcolor=\"#333333\", fontcolor=\"#FFFFFF\" ];");
		if (nilConnected)
			printNode(stream, "nil", id.get("nil"));
		
		stream.append("node [shape=Mrecord, style=filled, fontcolor=\"#000000\" fillcolor=\"#DDDDDD\", color=\"#DDDDDD\"];\n");
		
		for(Object node : nodes) { 
			printNode(stream, node, "<" + node + ">" + id.get(node) + "| data: " + id.get(dataMap.get(node)));
		}
		
		printEdge(stream, "head", thisListAtom, eval.evaluate(thisList.join(head)).iterator().next().atom(0));
		
		final TupleSet nextTuples = eval.evaluate(next);
		for(Object node : nodes) {
			for(Tuple t : nextTuples) { 
				if (t.atom(0).equals(node)) {
					printEdge(stream, "next", t.atom(0), t.atom(1));
				}
			}
		}
		
		stream.append("}\n"); 
	}

	
	private static java.util.List<Object> sort(final TupleSet tuples) {
		assert tuples.arity() == 2;
		final Set<Object> nodes = new LinkedHashSet<Object>();
		for(Tuple t : tuples) { 
			nodes.add(t.atom(0));
			nodes.add(t.atom(1));
		}
		final ArrayList<Object> sorted = new ArrayList<Object>(nodes);
		Collections.sort(sorted, new Comparator<Object>() {
			final TupleFactory tf = tuples.universe().factory();
			public int compare(Object o1, Object o2) {
				if (o1.equals(o2))
					return 0;
				else if (tuples.contains(tf.tuple(o1, o2)))
					return -1;
				else if (tuples.contains(tf.tuple(o2, o1)))
					return 1;
				return o1.toString().compareTo(o2.toString());
			}
		});
		return sorted;
	}
	
	private static Map<Object, Object> functionToMap(TupleSet tuples) { 
		assert tuples.arity() == 2;
		final Map<Object, Object> out = new LinkedHashMap<Object, Object>();
		for(Tuple t : tuples) { 
			out.put(t.atom(0), t.atom(1));
		}
		return out;
	}
	
	private static void printNode(PrintStream stream, Object node, String name) {
		stream.append(node.toString());
		stream.append("[ label=\"" );
		stream.append(name);
		stream.append("\" ];\n");
	}
	
	private static void printEdge(PrintStream stream, String name, Object start, Object end) {
		stream.append(start.toString());
		stream.append(" -> ");
		stream.append(end.toString());
		stream.append(" [ label=\"");
		stream.append(name);
		stream.append("\"];\n");
	}
	
	
	
	static final void printEncoding(ListEncoding enc) {
		
		System.out.println("\n-----------trace expressions-----------");
		System.out.println("assume invariants(this, next, data, head) && this.head != null && this.head.next != null : ");
		System.out.println(PrettyPrinter.print(enc.pre(), 2));
		System.out.println("next = "+ enc.next);
		System.out.println("head = "+ enc.head);
		
		System.out.println("\nnearNode0 = "+ enc.nearNode0());
		System.out.println("midNode0 = "+ enc.midNode0());
		System.out.println("farNode0 = "+ enc.farNode0());
		
		System.out.println("\nnext0 = "+ enc.next0());
		
		System.out.println("\nguard0 (farNode0 != null) = "+ enc.guard0());
		System.out.println("next1 = "+ enc.next1());
		System.out.println("nearNode1 = "+ enc.nearNode1());
		System.out.println("midNode1 = "+ enc.midNode1());
		System.out.println("farNode1 = "+ enc.farNode1());
		
		System.out.println("\nnext2 = "+ enc.next2());
		System.out.println("nearNode2 = "+ enc.nearNode2());
		System.out.println("midNode2 = "+ enc.midNode2());
		System.out.println("farNode2 = "+ enc.farNode2());
		System.out.println("assume loopGuard (farNode2 = null) : " + enc.loopGuard());
		
		System.out.println("\nnext3 = "+ enc.next3());
		System.out.println("head0 = "+ enc.head0());
		
		System.out.println("\nassert invariants(this, next3, data, head0) &&\n"+
				"(let nodes = this.head.*next, nodes' = this.head0.*next3, ns = nodes - nil |\n" +
				"  nodes' = nodes and next3 & (ns -> ns) = ~(next & (ns -> ns))) :" );
		System.out.println(PrettyPrinter.print(enc.post(), 2));
		System.out.println();
	}
	
	static final void printInstance(ListEncoding enc, Instance inst) { 
		if (inst == null) return;
		final Evaluator eval = new Evaluator(inst);
		
		System.out.println("-----------invariant state-----------");
		for(Relation r : new Relation[]{ enc.list, enc.node, enc.string, enc.data, enc.thisList }) {
			System.out.println(r + " = "+ eval.evaluate(r));
		}

		
		System.out.println("\n-----------trace-----------");
		System.out.println("assume invariants(this, next, data, head) && this.head != null && this.head.next != null : " + 
				eval.evaluate(enc.pre()));
		System.out.println("next = "+ eval.evaluate(enc.next));
		System.out.println("head = "+ eval.evaluate(enc.head));
		
		System.out.println("\nnearNode0 = "+ eval.evaluate(enc.nearNode0()));
		System.out.println("midNode0 = "+ eval.evaluate(enc.midNode0()));
		System.out.println("farNode0 = "+ eval.evaluate(enc.farNode0()));
		
		System.out.println("\nnext0 = "+ eval.evaluate(enc.next0()));
		
		System.out.println("\nguard0 (farNode0 != null) = "+ eval.evaluate(enc.guard0()));
		System.out.println("next1 = "+ eval.evaluate(enc.next1()));
		System.out.println("nearNode1 = "+ eval.evaluate(enc.nearNode1()));
		System.out.println("midNode1 = "+ eval.evaluate(enc.midNode1()));
		System.out.println("farNode1 = "+ eval.evaluate(enc.farNode1()));
		
		System.out.println("\nnext2 = "+ eval.evaluate(enc.next2()));
		System.out.println("nearNode2 = "+ eval.evaluate(enc.nearNode2()));
		System.out.println("midNode2 = "+ eval.evaluate(enc.midNode2()));
		System.out.println("farNode2 = "+ eval.evaluate(enc.farNode2()));
		System.out.println("assume loopGuard (farNode2 = null) : " + eval.evaluate(enc.loopGuard()));
		
		System.out.println("\nnext3 = "+ eval.evaluate(enc.next3()));
		System.out.println("head0 = "+ eval.evaluate(enc.head0()));
		
		System.out.println("\nassert invariants(this, next3, data, head0) &&\n"+
				"(let nodes = this.head.*next, nodes' = this.head0.*next3, ns = nodes - nil |\n" +
				"  nodes' = nodes and next3 & (ns -> ns) = ~(next & (ns -> ns))) : " +  eval.evaluate(enc.post()));
	}
	
	
}
