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
package kodkod.examples.sudoku;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 * A utility for parsing various String specifications of Sudoku puzzles.
 * @author Emina Torlak
 */
public final class SudokuParser {
	private SudokuParser() {}
	
	private static String[] split(String puzzle) { 
		final String[] parsed = puzzle.split("\\s+");
		return (parsed.length>1) ? parsed : puzzle.replaceAll("(\\d)", "$1 ").split(" ");
	}
		
	/**
	 * Returns the representation of the clues encoded in the given array as 
	 * an NxNxN tuple set drawn from the given universe.  N is assumed
	 * to be a perfect square, and the universe is assumed to consist of Integer objects in 
	 * the range [1..N]. The  array is assumed to consist of N*N numbers, drawn 
	 * from the set 0..N, inclusive, where a consecutive sequence of N
	 * numbers represents one row of an NxN Sudoku grid.
	 * Zeros stand for blank entries.  
	 * @requires some r: int | puzzle.length = r * r * r * r
	 * @requires universe.atoms[int] = {i: Integer | 1 <= i.intValue() <= puzzle.length} 
	 * @return a tupleset representation of the clues in the puzzle specified by the given array.
	 */
	public static final TupleSet parse(String[] puzzle, Universe univ) { 
		final int n = (int)StrictMath.sqrt(puzzle.length);
		final int r = (int)StrictMath.sqrt(n);
		if (puzzle.length!=r*r*r*r)  throw new IllegalArgumentException("Not a valid puzzle spec: expected " + (r*r*r*r) + " numbers but found " + puzzle.length);
				
		final TupleFactory f = univ.factory();
		
		final TupleSet givens = f.noneOf(3);
		
		for(int i = 0; i < n; i++) { 
			for(int j = 0; j < n; j++) { 
				try {
					final int digit = Integer.parseInt(puzzle[i*n+j]);
					if (digit>0 && digit<=n) {
						final Tuple t = f.tuple(i+1, j+1, digit);
						givens.add(t);
					} else if (digit>n) { 
						throw new IllegalArgumentException("Not a valid puzzle spec: expected numbers from [0, " + n+"] but found "+digit);
					} 
				} catch (NumberFormatException nfe) { 
					throw new IllegalArgumentException("Not a valid puzzle spec: expected numbers from [0, " + n+"] but found "+puzzle[i*n+j]);
				}
			}
		}
		
		return givens;
	}
	
	/**
	 * Returns the representation of the clues encoded in the given array as 
	 * an NxNxN tuple set drawn from a freshly constructed universe.  N is assumed
	 * to be a perfect square, and the universe consist of Integer objects in 
	 * the range [1..N]. The  array is assumed to consist of N*N numbers, drawn 
	 * from the set 0..N, inclusive, where a consecutive sequence of N
	 * numbers represents one row of an NxN Sudoku grid.
	 * Zeros stand for blank entries.  
	 * @requires some r: int | puzzle.length = r * r * r * r
	 * @return a tupleset representation of the clues in the puzzle specified by the given array.
	 */
	public static final TupleSet parse(String[] puzzle) { 
		final Integer[] atoms = new Integer[(int)StrictMath.sqrt(puzzle.length)];
		for(int i = 0; i < atoms.length; i++) { atoms[i] = i+1; }
		return parse(puzzle, new Universe((Object[])atoms));
	}
	
	/**
	 * Parses the given puzzle string and returns the representation of
	 * the encoded clues as an NxNxN tuple set drawn from a freshly constructed universe.
	 * N is assumed to be a perfect square, and the universe consists of Integer objects
	 * in the range [1..N].  If N>9, this method assumes that the puzzle 
	 * string consists of N*N space-separated numbers, drawn 
	 * from the set 0..N, inclusive, where a consecutive sequence of N
	 * space-separated numbers represents one row of an NxN Sudoku grid.
	 * Zeros stand for blank entries.  If N<=9, then the spaces may be omitted.
	 * @requires some r: [2..) | (puzzle.split("\\s+").length() = r * r * r * r) || (r<=3 && puzzle.length = r * r * r * r)
	 * @return a tupleset representation of the clues in the puzzle specified by the given string.
	 */
	public static final TupleSet parse(String puzzle) { 
		final String[] parsed = split(puzzle);
		final Integer[] atoms = new Integer[(int)StrictMath.sqrt(parsed.length)];
		for(int i = 0; i < atoms.length; i++) { atoms[i] = i+1; }
		return parse(parsed, new Universe((Object[])atoms));
	}
	
	/**
	 * Parses the given puzzle string and returns the representation of
	 * the encoded clues as an NxNxN tuple set drawn from the given universe.  N is assumed
	 * to be a perfect square, and the universe is assumed to consist of Integer objects in 
	 * the range [1..N]. If N>9, the puzzle string is assumed to consist of N*N space-separated numbers, drawn 
	 * from the set 0..N, inclusive, where a consecutive sequence of N
	 * space-separated numbers represents one row of an NxN Sudoku grid.
	 * Zeros stand for blank entries.  If N<=9, then the spaces may be omitted.
	 * @requires some r: [2..) | (puzzle.split("\\s+").length() = r * r * r * r) || (r<=3 && puzzle.length = r * r * r * r)
	 * @requires universe.atoms[int] = {i: Integer | 1 <= i.intValue() <= max(puzzle.split("\\s+").length(), puzzle.length())} 
	 * @return a tupleset representation of the clues in the puzzle specified by the given string.
	 */
	public static final TupleSet parse(String puzzle, Universe univ) { 
		return parse(split(puzzle), univ);
	}
	
	/**
	 * Returns a string representation of the given puzzle.
	 * @requires some r: int | puzzle.universe.atoms[int] = { i: Integer | 1 <= i.intValue() <= r*r } 
     * @requires puzzle.arity = 3   
	 * @return a string representation of the given puzzle
	 */
	public static final String toString(TupleSet puzzle) { 
		final StringBuilder str = new StringBuilder();
		final int n = puzzle.universe().size();
		final String sep = (n>9) ? " " : "";
		Iterator<Tuple> itr = puzzle.iterator();
		if (!itr.hasNext()) { 
			str.append(0);
			for(int i = 1, max = n*n; i < max; i++) { 
				str.append(sep+0);
			}
			return str.toString();
		}
		
		int last = 0;
		Tuple tuple = itr.next();
		if ((Integer)tuple.atom(0)==1 && (Integer)tuple.atom(1)==1) { 
			str.append(tuple.atom(2));
		} else {
			str.append(0);
			itr = puzzle.iterator();
		}
		
		while(itr.hasNext()) { 
			tuple = itr.next();
			final int current = n*((Integer)tuple.atom(0)-1) + ((Integer)tuple.atom(1)-1);
			for(int i = last+1; i < current; i++) { 
				str.append(sep+0);
			}
			str.append(sep+tuple.atom(2));
			last = current;
		}

		for(int i = last+1, max = n*n; i < max; i++) { 
			str.append(sep+0);
		}
		return str.toString();
	}
	
	private static void appendDivider(StringBuilder str, int r) { 
		final String len = (r<=3) ? "--" : "---";
		for(int i = 0; i < r; i++) { 
			str.append("+-");
			for(int j = 0; j < r; j++) { 
				str.append(len);
			}
		}
		str.append("+\n");
	}
	
	/**
	 * Returns a pretty-printed string of the given sudoku solution.
	 * @requires solution is a valid sudoku solution
	 * @requires some r: int | solution.universe = { i: Integer | 1 <= i.intValue() <= r*r }
	 * @return a pretty-printed string of the given sudoku solution
	 */
	public static final String prettyPrint(TupleSet solution) { 
		final StringBuilder str = new StringBuilder();
		final int n = solution.universe().size();
		final int r = (int)Math.sqrt(n);
		appendDivider(str, r);
		final Iterator<Tuple> psol = solution.iterator();
		for(int i = 1; i <= n; i++) {
			str.append("| ");
			for(int j = 0; j < r; j++) {
				for(int k = 0; k < r; k++) {
					final int atom = (Integer)psol.next().atom(2);
					if (atom<10&&r>3) str.append(" ");
					str.append(atom);
					str.append(" ");
				}
				str.append("| ");
			}
			str.append("\n");
			if (i%r==0)	appendDivider(str, r);		
		}
		return str.toString();
	}
	
	/**
	 * Returns a map that maps each option in the given argument array to its value, 
	 * or null if the option has no value.
	 * Assumes that all options are of the form "-opt=val" or "-opt". 
	 * @return a map that maps each option in the given argument array to its value, 
	 * or null if the option has no value.
	 */
	static Map<String, String> options(String[] args) { 
		final Map<String,String> opts = new LinkedHashMap<String,String>();
		for(String arg: args) { 
			if (arg.startsWith("-")) { 
				String[] opt = arg.split("=");
				switch(opt.length) { 
				case 1 : opts.put(opt[0], null); break;
				case 2 : opts.put(opt[0], opt[1]); break;
				default : throw new IllegalArgumentException("Unrecognized option format: " + arg);
				}
			}
		}
		return opts;
	}
	
}
