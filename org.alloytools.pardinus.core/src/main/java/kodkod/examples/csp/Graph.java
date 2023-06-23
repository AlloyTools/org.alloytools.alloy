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
package kodkod.examples.csp;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * A simple graph implementation for parsing and storing  graphs in DIMACS and ASP formats.
 * @specfield nodes: set N
 * @specfield edges: nodes->nodes
 * @specfield start: nodes+null
 * @invariant all e: edges | e.from + e.to in nodes
 * @author Emina Torlak
 */
public final class Graph<N> {

	private final Map<N,Set<N>> graph;
	private final N start;
	/**
	 * Constructs a graph that stores the given sets of nodes and edges,
	 * along with the specified distinguished start node, if any.
	 * @requires start in graph.keySet() + null
	 * @ensures this.start' = start && this.nodes = graph.keySet() && this.edges = graph
	 */
	private Graph(N start, Map<N,Set<N>> graph) { 
		this.start = start;
		this.graph = Collections.unmodifiableMap(graph);
	}
	
	/**
	 * Returns the nodes.
	 * @return this.nodes
	 */
	public Set<N> nodes() { return graph.keySet(); }
	
	/**
	 * Returns the start node.
	 * @return this.start
	 */
	public N start() { return start; }
	
	/**
	 * Returns this.edges[n]
	 * @return this.edges[n]
	 */
	public Set<N> edges(Object node) { return graph.containsKey(node) ? Collections.unmodifiableSet(graph.get(node)) : null; }
		
	/**
	 * Supported graph file formats.
	 * @author Emina Torlak
	 */
	public static enum Format {
		/**
		 * DIMACS graph format. 
		 */
		DIMACS {
			/**
			 * {@inheritDoc}
			 * @see kodkod.examples.csp.Graph.Format#parse(java.lang.String)
			 */
			public Graph<Integer> parse(String file) { 
				try(BufferedReader in = new BufferedReader(new FileReader(file))) {
					final Map<Integer,Set<Integer>> graph = new LinkedHashMap<Integer,Set<Integer>>();

					
					int vertices = -1;
					final Pattern p = Pattern.compile("p\\s+edge\\s+(\\d+)\\s+(\\d+)\\s*");
					final Matcher mp = p.matcher("");
					for(String line = in.readLine(); line != null; line = in.readLine()) { 
						mp.reset(line);
						if(mp.matches()) { 
							vertices = Integer.parseInt(mp.group(1));
							break;
						} 
					}
					if (vertices<0) throw new IllegalArgumentException("Bad header line: " + file);
					for(int i = 0; i < vertices; i++) { 
						graph.put(i+1, new LinkedHashSet<Integer>(4));
					}
					
					final Pattern e = Pattern.compile("e\\s+(\\d+)\\s+(\\d+)\\s*");
					final Matcher me = e.matcher("");
					
					for(String line = in.readLine(); line != null; line = in.readLine()) { 
						me.reset(line);
						if(me.matches()) { 
							final int from = Integer.parseInt(me.group(1)), to = Integer.parseInt(me.group(2));
							if (!graph.containsKey(from)) throw new IllegalArgumentException("Bad vertex: " + from + " in " + line);
							if (!graph.containsKey(to)) throw new IllegalArgumentException("Bad vertex: " + to + " in " + line);
							graph.get(from).add(to); 
							graph.get(to).add(from);
						} 			
					}
 					return new Graph<Integer>(null, graph);					
				} catch (IOException e) {
					throw new IllegalArgumentException("Bad file: " + file);
				} 
			}
		},
		
		/**
		 * Full ASP graph format; used for Hamiltonian path instances (http://asparagus.cs.uni-potsdam.de/?action=instances&id=30).
		 */
		ASP {
			/**
			 * {@inheritDoc}
			 * @see kodkod.examples.csp.Graph.Format#parse(java.lang.String)
			 */
			public Graph<String> parse(String file) {
				try(BufferedReader in = new BufferedReader(new FileReader(file))) {
					
					final Map<String,Set<String>> graph = new LinkedHashMap<String,Set<String>>();
					String start = null;
					
					final Pattern v = Pattern.compile("vtx\\((\\S+)\\)\\.");
					final Matcher mv = v.matcher("");
					final Pattern e = Pattern.compile("edge\\((\\S+),(\\S+)\\)\\.");
					final Matcher me = e.matcher("");
					final Pattern s = Pattern.compile("start\\((\\S+)\\)\\.");
					final Matcher ms = s.matcher("");
					
					for(String line = in.readLine(); line != null; line = in.readLine()) { 
						mv.reset(line);
						while(mv.find()) { 
							graph.put(mv.group(1), new LinkedHashSet<String>(4));
						}
						me.reset(line);
						while(me.find()) { 
							final String from = me.group(1), to = me.group(2);
							if (!graph.containsKey(from)) throw new IllegalArgumentException("Bad vertex: " + from + " in " + line);
							if (!graph.containsKey(to)) throw new IllegalArgumentException("Bad vertex: " + to + " in " + line);
							graph.get(from).add(to); 
							graph.get(to).add(from);
						}
						ms.reset(line);
						if (ms.find()) { start = ms.group(1); }
					}
					if (graph.isEmpty()) throw new IllegalArgumentException("No vertices or edges found in " + file);
					return new Graph<String>(start, graph);
					
				} catch (IOException e) {
					throw new IllegalArgumentException(e);
				}
			}
		},
		
		/**
		 * ASP graph format where only edges are specified; used for coloring instances (http://asparagus.cs.uni-potsdam.de/?action=instances&id=30).
		 */
		ASP_EDGES {
			/**
			 * {@inheritDoc}
			 * @see kodkod.examples.csp.Graph.Format#parse(java.lang.String)
			 */
			public Graph<String> parse(String file) {
				try(BufferedReader in = new BufferedReader(new FileReader(file))) {
				
					final Map<String,Set<String>> graph = new LinkedHashMap<String,Set<String>>();
					String start = null;
					
					final Pattern e = Pattern.compile("edge\\((\\S+),(\\S+)\\)\\.");
					final Matcher me = e.matcher("");
					
					for(String line = in.readLine(); line != null; line = in.readLine()) { 
						me.reset(line);
						while(me.find()) { 
							final String from = me.group(1), to = me.group(2);
							if (!graph.containsKey(from)) {
								graph.put(from, new LinkedHashSet<String>(4));
							}
							if (!graph.containsKey(to)) {
								graph.put(to, new LinkedHashSet<String>(4));
							}
							graph.get(from).add(to); 
//							graph.get(to).add(from);
						}
					}
					if (graph.isEmpty()) throw new IllegalArgumentException("No vertices or edges found in " + file);
					return new Graph<String>(start, graph);
					
				} catch (IOException e) {
					throw new IllegalArgumentException("Bad file: " + file);
				}
			}
		};
		
		/**
		 * Parses the given file into a graph
		 * @requires the file must be in the format specified by this
		 * @return a graph parsed out of the given file.
		 */
		public abstract Graph<?> parse(String file);
	}
	
}
