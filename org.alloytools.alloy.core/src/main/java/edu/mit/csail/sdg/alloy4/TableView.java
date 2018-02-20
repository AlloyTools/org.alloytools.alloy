package edu.mit.csail.sdg.alloy4;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class TableView {
	final static String		SUPERSCRIPTS	= "⁰¹²³⁴⁵⁶⁷⁸⁹";
	final static String		SUBSCRIPTS		= "₀₁₂₃₄₅₆₇₈₉";
	final static String		BOX_SINGLE		= "│┌─┬┐┘┴└├┼┤";
	final static Pattern	TABLE_P			= Pattern.compile("\\s*\\{(([\\d\\w$\\s,>-]+))\\}\\s*");

	public static boolean isTable(String input) {
		return TABLE_P.matcher(input).matches();
	}

	public static String toTable(String s, boolean header) {
		Set<String> multiple = new HashSet<>();

		boolean multicolumn = false;
		s = s.trim();
		s = s.substring(1, s.length() - 1);
		String clauses[] = s.split("\\s*,\\s*");
		List<List<String>> data = new ArrayList<>();
		for (String clause : clauses) {
			String atoms[] = clause.split("\\s*->\\s*");
			ArrayList<String> l = new ArrayList<String>();
			data.add(l);
			for (String atom : atoms) {
				atom = toScriptedString(atom, multiple);
				l.add(atom);
			}
			multicolumn |= l.size() > 1;
		}

		for ( List<String> l : data) {
			for ( int i=0; i<l.size(); i++) {
				String cell = l.get(i);
				String name = getName(cell);
				if ( !multiple.contains(name))
					l.set(i, name);
			}
		}
		
		if (multicolumn) {
			return toTable(data, BOX_SINGLE, "", header);
		}

		data = transpose(data);
		return toTable(data, BOX_SINGLE, "⁻¹", header);
	}

	public static int getIndex(String cell) {
		String s = revertSuffix(cell);
		int n = s.lastIndexOf("$");
		if ( n < 0)
			return -1;
		
		String num = cell.substring(n+1);
		if (!num.matches("\\d+"))
			return -1;
		
		return Integer.parseInt(num);
	}

	public static String getName(String cell) {
		String s = revertSuffix(cell);
		int n = s.lastIndexOf("$");
		if ( n < 0)
			return cell;
		
		return cell.substring(0,n);		
	}
	private static List<List<String>> transpose(List<List<String>> data) {
		List<List<String>> result = new ArrayList<>();
		for (List<String> l : data) {
			int n = 0;
			for (String s : l) {
				if (result.size() <= n) {
					result.add(new ArrayList<String>());
				}
				result.get(n).add(s);
			}
		}
		return result;
	}

	public static String toScriptedString(String atom) {
		return toScriptedString(atom, null);
	}

	public static String toScriptedString(String atom, Set<String> multiple) {

		if (atom.matches(".*\\$\\d+")) {
			StringBuilder sb = new StringBuilder();
			int n = atom.lastIndexOf("$");
			String prefix = atom.substring(0, n);
			sb.append(prefix);
			for (int i=n+1; i < atom.length(); i++) {
				sb.append(SUPERSCRIPTS.charAt(atom.charAt(i) - '0'));
			}

			if (multiple != null) {
				
				int suffix = Integer.parseInt(atom.substring(n + 1));
				if (suffix != 0)
					multiple.add(prefix);
			}
			return sb.toString();
		}
		return atom;
	}

	public static String toTable(List<List<String>> data, String box, String lefthead, boolean header) {
		List<Integer> widths = calcWidths(data);
		StringBuilder sb = new StringBuilder();
		firstline(sb, widths, box, lefthead);
		String lastFirstColumn = null;

		for (List<String> row : data) {
			int i = 0;
			char del = box.charAt(0);
			for (String cell : row) {
				if (i == 0) {
					if (lastFirstColumn == null || !lastFirstColumn.equals(cell))
						lastFirstColumn = cell;
					else
						cell = "";
				}

				int w = widths.get(i);
				if (cell.matches("-?\\d+")) {
					sb.append(del);
					width(sb, w - cell.length(), " ");
					sb.append(cell);
				} else {
					sb.append(del).append(cell);
					width(sb, w - cell.length(), " ");
				}
				del = box.charAt(0);
				i++;
			}
			sb.append(box.charAt(0) + "\n");
			if (header && data.size() > 1) {
				separatorLine(sb, widths, box);
				header = false;
			}
		}
		lastline(sb, widths, box);
		return sb.toString();
	}

	private static void width(StringBuilder sb, int i, String c) {
		while (i-- > 0)
			sb.append(c);
	}

	private static void firstline(StringBuilder sb, List<Integer> widths, String box, String lefthead) {
		char del = box.charAt(1);
		for (int w : widths) {
			sb.append(del);
			width(sb, w, "" + box.charAt(2));
			del = box.charAt(3);
		}
		sb.append(box.charAt(4) + lefthead + "\n");
	}

	private static void separatorLine(StringBuilder sb, List<Integer> widths, String box) {
		char del = box.charAt(8);
		for (int w : widths) {
			sb.append(del);
			width(sb, w, "" + box.charAt(2));
			del = box.charAt(9);
		}
		sb.append(box.charAt(10) + "\n");
	}

	private static void lastline(StringBuilder sb, List<Integer> widths, String box) {
		char del = box.charAt(7);
		for (int w : widths) {
			sb.append(del);
			width(sb, w, "" + box.charAt(2));
			del = box.charAt(6);
		}
		sb.append(box.charAt(5) + "\n");
	}

	private static List<Integer> calcWidths(List<List<String>> data) {
		List<Integer> widths = new ArrayList<>();
		for (List<String> row : data) {
			int i = 0;
			for (String cell : row) {
				while (widths.size() <= i) {
					widths.add(0);
				}
				if (cell.length() > widths.get(i)) {
					widths.set(i, cell.length());
				}
				i++;
			}
		}
		return widths;
	}

	/**
	 * Turn a super scripted name back
	 * 
	 * @param cmd
	 * @return
	 */
	static Pattern SUPERSCRIPTED_NAME_P = Pattern.compile("(\\p{javaJavaIdentifierPart}+)([⁰¹²³⁴⁵⁶⁷⁸⁹]+)");

	public static String revertSuffix(String cmd) {

		StringBuffer sb = new StringBuffer();
		Matcher matcher = SUPERSCRIPTED_NAME_P.matcher(cmd);
		while (matcher.find()) {
			String suffix = matcher.group(2);
			int n = 0;
			for (int i = 0; i < suffix.length(); i++) {
				char c = suffix.charAt(i);
				n = 10 * n + SUPERSCRIPTS.indexOf(c);
			}
			matcher.appendReplacement(sb, matcher.group(1) + "\\$" + n);
		}
		matcher.appendTail(sb);
		return sb.toString();
	}

}
