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

import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Random;

import kodkod.instance.TupleSet;
import kodkod.instance.Universe;
import kodkod.util.ints.IntBitSet;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;

/**
 * A class for managing NxN (where N is a perfect square) Sudoku puzzles loaded from a file.
 * @specfield N, size : int
 * @specfield puzzles: [0..size) ->one TupleSet
 * @invariant some r: int | r*r = N
 * @invariant all p1, p2: puzzles | p1.universe = p2.universe
 * @invariant all p: puzzles[int] | p.arity = 3 and p.universe = { i: Integer | 1 <= i.intValue() <= N } 
 * @author Emina Torlak
 */
public final class SudokuDatabase implements Iterable<TupleSet>{
	private final TupleSet[] puzzles;
	
	private SudokuDatabase(String[] puzzles) { 
		this.puzzles = new TupleSet[puzzles.length];
		if (puzzles.length>0) { 
			this.puzzles[0] = SudokuParser.parse(puzzles[0]);
			final Universe univ = this.puzzles[0].universe();
			for(int i = 1; i < puzzles.length; i++) { 
				this.puzzles[i] = SudokuParser.parse(puzzles[i], univ);
			}
		}
	}
		
	/**
	 * Constructs a new sudoku database out of the given collection of puzzles.
	 * Each tupleset in the given collection is assumed to be drawn from the same
	 * universe, to have arity 3, and to have all of its tuples drawn from the subset
	 * {1..N} of the given universe where N is a perfect square.
	 * @requires all p1, p2: puzzles | p1.universe = p2.universe
	 * @requires some r: int | all p: puzzles | p.arity = 3 and p.universe = { i: Integer | 1 <= i.intValue() <= r*r }  
	 * @ensures this.puzzles' = puzzles.toArray()
	 */
	private SudokuDatabase(Collection<TupleSet> puzzles) { 
		this.puzzles = puzzles.toArray(new TupleSet[puzzles.size()]);
	}
	
	/**
	 * Returns the size of this database.
	 * @return #this.puzzles
	 */
	public int size() { return puzzles.length; }
	
	/**
	 * Returns the clues for ith puzzle.  
	 * @requires 0 <= i < this.size() 
	 * @return this.puzzles[i]
	 */
	public TupleSet puzzle(int i) { return this.puzzles[i].clone(); }
	
	/**
	 * Returns an iterator over the puzzles in this database.  The returned
	 * iterator does not support removal.
	 * @return iterator over the puzzles in this database.
	 */
	public Iterator<TupleSet> iterator() { 
		return new Iterator<TupleSet>() {
			private int i = 0;
			public boolean hasNext() { return i < puzzles.length; }
			public TupleSet next() {
				if (!hasNext()) throw new NoSuchElementException();
				return puzzle(i++);
			}
			public void remove() { throw new UnsupportedOperationException(); }
		};
	}
	
	/**
	 * Writes out this database to the given file.  Each puzzle is written out
	 * as a string of N*N numbers, where each subsequence of N numbers represents one row
	 * of the grid and zeros stand for blanks.
	 * @throws IOException 
	 */
	public void write(String file) throws IOException { 
		write(new BufferedOutputStream(new FileOutputStream(file)));
	}
	
	/**
	 * Writes out this database to the stream.  Each puzzle is written out
	 * as a string of N*N numbers, where each subsequence of N numbers represents one row
	 * of the grid and zeros stand for blanks.
	 * @throws IOException 
	 */
	public void write(OutputStream stream) throws IOException {
		if (puzzles.length==0) return;
		final PrintWriter writer = new PrintWriter(stream);
		for(TupleSet puzzle : puzzles) { 
			writer.println(SudokuParser.toString(puzzle));
		}
		writer.close();
	}
	
	/**
	 * Loads the puzzles from the given file into a fresh database.
	 * This method assumes that each line of the file represents
	 * an individual puzzle.  The puzzle should be given as a string of 
	 * N*N numbers, where each subsequence of N numbers represents one row
	 * of the grid and zeros stand for blanks. If N > 9, the numbers should
	 * be separated by spaces or tabs.  If N <= 9, the spaces may be omitted. 
	 * @requires the file is formatted as described above
	 * @return a sudoku database with the puzzles from the given file
	 * @throws IOException 
	 */
	public static SudokuDatabase load(String file) throws IOException { 
		final List<TupleSet> puzzles = new ArrayList<TupleSet>(100);
		final BufferedReader reader = new BufferedReader(new FileReader(file));
		String puzzle = reader.readLine();
		if (puzzle!=null) { 
			puzzles.add(SudokuParser.parse(puzzle));
			final Universe univ = puzzles.get(0).universe();
			while((puzzle=reader.readLine())!=null) { 
				puzzles.add(SudokuParser.parse(puzzle, univ));
			}
		}
		reader.close();
		return new SudokuDatabase(puzzles);
	}

	/**
	 * Extract the puzzles with the specified indices from the given file and 
	 * returns them in a database. This method assumes that each line of the file represents
	 * an individual puzzle.  The puzzle should be given as a string of 
	 * N*N numbers, where each subsequence of N numbers represents one row
	 * of the grid and zeros stand for blanks. If N > 9, the numbers should
	 * be separated by spaces or tabs.  If N <= 9, the spaces may be omitted. 
	 * @requires the file is formatted as described above
	 * @requires the indices of puzzles requested are non-negative and do not exceed the number of puzzles in the file
	 * @return a sudoku database with the specified puzzles extracted from the given file
	 * @throws IOException 
	 */
	@SuppressWarnings("unchecked")
	public static SudokuDatabase load(String file, IntSet indices) throws IOException {
		if (indices.isEmpty()) return new SudokuDatabase(Collections.EMPTY_LIST);
		if (indices.min()<0) throw new IllegalArgumentException("Negative indices not permitted: " + indices.min());
		
		final int numPuzzles = indices.size();
		final String[] puzzles = new String[numPuzzles];
		try (BufferedReader reader = new BufferedReader(new FileReader(file))) {
	
			final IntIterator randItr = indices.iterator();
			for(int i=0, last = -1; i<numPuzzles; i++) { 
				final int next = randItr.next();
				for(int j = last+1; j<next; j++) { 
					reader.readLine(); // discard
				}
				last = next;
				puzzles[i] = reader.readLine();
				if (puzzles[i]==null) { 
					throw new IllegalArgumentException("The file " + file + " contains fewer than " + next + " puzzles.");
				}
			}
		}
		 
		return new SudokuDatabase(puzzles);
	}
	
	/**
	 * Randomly selects the given number of puzzles from the specified 
	 * file, and returns them in a database.  The random number generator
	 * is initialized with the current time.
	 * This method assumes that each line of the file represents
	 * an individual puzzle.  The puzzle should be given as a string of 
	 * N*N numbers, where each subsequence of N numbers represents one row
	 * of the grid and zeros stand for blanks. If N > 9, the numbers should
	 * be separated by spaces or tabs.  If N <= 9, the spaces may be omitted. 
	 * @requires the file is formatted as described above
	 * @requires the number of puzzles requested does not exceed the number of puzzles in the file
	 * @return a sudoku database with the given number of puzzles, randomly 
	 * selected from the specified file
	 * @throws IOException 
	 */
	public static SudokuDatabase loadRandom(String file, int puzzles) throws IOException { 
		return loadRandom(file, puzzles, System.currentTimeMillis());
	}
	
	/**
	 * Randomly selects the given number of puzzles from the specified 
	 * file, and returns them in a database.  The random number generator
	 * is initialized with the given seed.  
	 * This method assumes that each line of the file represents
	 * an individual puzzle.  The puzzle should be given as a string of 
	 * N*N numbers, where each row of N numbers represents one row
	 * of the grid and zeros stand for blanks. If N > 9, the numbers should
	 * be separated by spaces or tabs.  If N <= 9, the spaces may be omitted. 
	 * @requires the file is formatted as described above
	 * @requires the number of puzzles requested does not exceed the number of puzzles in the file
	 * @return a sudoku database with the given number of puzzles, randomly 
	 * selected from the specified file using the specified seed.
	 * @throws IOException 
	 */
	public static SudokuDatabase loadRandom(String file, int numPuzzles, long seed) throws IOException { 
	
		final Random rand = new Random(seed);
		final IntSet rands = new IntBitSet(numPuzzles);
		while(rands.size()<numPuzzles) { 
			rands.add(rand.nextInt(numPuzzles));
		}
		
		return load(file, rands);
	}

	private static void usage() {
		System.out.println("Usage: java examples.sudoku.SudokuDatabase [-seed=<seed>] [-puzzles=<number of puzzles>] [-o=<output filename>] <database file>");
		System.exit(1);
	}
	/**
	 * Usage: java examples.sudoku.SudokuDatabase [-seed=<seed>] [-puzzles=<number of puzzles>] [-o=<output filename>] <database file> 
	 */
	public static void main(String[] args) { 
		if (args.length<1) usage();
		final String file = args[args.length-1];
		final Map<String,String> opts = SudokuParser.options(args);
		
		try {
			final SudokuDatabase db;
			if (opts.containsKey("-puzzles")) { 
				final String numString = opts.get("-puzzles");
				if (numString==null) usage();
				final int numPuzzles = Integer.parseInt(numString);
				if (opts.containsKey("-seed")) { 
					final String seedString = opts.get("-seed");
					if (seedString==null) usage();
					final long seed = Long.parseLong(seedString);
					db = loadRandom(file, numPuzzles, seed);
				} else {
					db = loadRandom(file, numPuzzles);
				}
			} else {
				db = load(file);
			}
			if (opts.containsKey("-o")) { 
				final String oString = opts.get("-o");
				if (oString==null) usage();
				db.write(oString);
			} else {
				db.write(System.out);
			}
		} catch (NumberFormatException nfe) { 
			usage(); 
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}
