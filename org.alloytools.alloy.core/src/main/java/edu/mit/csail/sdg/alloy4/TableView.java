package edu.mit.csail.sdg.alloy4;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Pattern;

public class TableView {
	final static String SUPERSCRIPTS = "⁰¹²³⁴⁵⁶⁷⁸⁹";
	final static String SUBSCRIPTS = "₀₁₂₃₄₅₆₇₈₉";
	
	final static Pattern TABLE_P = Pattern.compile("\\s*\\{(([\\d\\w$\\s,>-]+))\\}\\s*");
	public static boolean isTable(String input) {
		return TABLE_P.matcher(input).matches();
	}
	
	public static String toTable( String s) {
		s = s.trim();
		s=s.substring(1, s.length()-1);
		String clauses[] = s.split("\\s*,\\s*");
		List<List<String>> data = new ArrayList<>();
		for  (String clause : clauses) {
			String atoms[] = clause.split("\\s*->\\s*");
			ArrayList<String> l = new ArrayList<String>();
			data.add( l);
			for ( String atom : atoms ) {
				atom = toScriptedString(atom);
				l.add(atom);
			}
		}
		return toTable( data );
	}

	public static String toScriptedString(String atom) {
		if ( atom.matches(".*\\$\\d+")) {
			StringBuilder sb = new StringBuilder();
			int  n = atom.lastIndexOf("$");
			sb.append(atom.substring(0,n));
			for ( n++; n<atom.length(); n++) {
				sb.append( SUPERSCRIPTS.charAt(atom.charAt(n)-'0'));
			}
			return sb.toString();
		}
		return atom;
	}

	public static String toTable(List<List<String>> data) {
		List<Integer> widths = calcWidths( data );
		
		StringBuilder sb = new StringBuilder();
		firstline(sb,widths);
		for ( List<String> row : data) {
			int i= 0;
			String del = "│";
			for ( String cell : row) {
				int w = widths.get(i);
				if ( cell.matches("-?\\d+")) {
					sb.append(del);
					width(sb,w-cell.length(), " ");
					sb.append(cell);				
				} else {
					sb.append(del).append(cell);				
					width(sb,w-cell.length(), " ");
				}
				del = "│";
				i++;
			}
			sb.append("│\n");
		}
		lastline(sb, widths);
		return sb.toString();
	}

	private static void width(StringBuilder sb, int i, String c) {
		while ( i-- > 0)
			sb.append(c);
	}

	private static void firstline(StringBuilder sb, List<Integer> widths) {
		String del = "┌";
		for ( int w : widths) {
			sb.append(del);
			width(sb,w,"─");
			del="┬";
		}
		sb.append("┐\n");
	}
	private static void middleline(StringBuilder sb, List<Integer> widths) {
		String del = "├";
		for ( int w : widths) {
			sb.append(del);
			width(sb,w,"─");
			del="┼";
		}
		sb.append("┤\n");
	}
	private static void lastline(StringBuilder sb, List<Integer> widths) {
		String del = "└";
		for ( int w : widths) {
			sb.append(del);
			width(sb,w,"─");
			del="┴";
		}
		sb.append("┘\n");
	}

	private static List<Integer> calcWidths(List<List<String>> data) {
		List<Integer> widths = new ArrayList<>();
		for ( List<String> row : data) {
			int i = 0;
			for ( String cell : row) {
				while (widths.size() <= i) {
					widths.add(0);
				}
				if ( cell.length() > widths.get(i)) {
					widths.set(i, cell.length());
				}
				i++;
			}
		}
		return widths;
	}
	
}
