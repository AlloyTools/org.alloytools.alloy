package edu.mit.csail.sdg.alloy4;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.alloytools.alloy.core.AlloyCore;
import org.alloytools.util.table.Table;

import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Type;
import edu.mit.csail.sdg.sim.SimAtom;
import edu.mit.csail.sdg.sim.SimTuple;
import edu.mit.csail.sdg.sim.SimTupleset;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.A4TupleSet;
import kodkod.instance.Instance;
import kodkod.instance.TupleSet;

/**
 *
 * @modified [electrum] adapted to focus on particular state
 *
 */
public class TableView {

    final static String  SUPERSCRIPTS = "⁰¹²³⁴⁵⁶⁷⁸⁹";
    final static String  SUBSCRIPTS   = "₀₁₂₃₄₅₆₇₈₉";
    final static String  BOX_SINGLE   = "│┌─┬┐┘┴└├┼┤";
    final static Pattern TABLE_P      = Pattern.compile("\\s*\\{(([\\d\\w$\\s,>\"/-]+))\\}\\s*");

    public static boolean isTable(String input) {
        return TABLE_P.matcher(input).matches();
    }

    public static Table toTable(String s, boolean header) {
        s = s.trim();
        s = s.substring(1, s.length() - 1);
        String clauses[] = s.split("\\s*,\\s*");

        List<SimTuple> l = new ArrayList<>();
        for (String tuple : clauses) {
            String strings[] = tuple.split("\\s*->\\s*");
            List<SimAtom> atoms = new ArrayList<>();
            for (String string : strings) {
                SimAtom atom = SimAtom.make(string);
                atoms.add(atom);
            }

            l.add(SimTuple.make(atoms));
        }
        SimTupleset make = SimTupleset.make(l);

        return toTable(make);
    }

    public static int getIndex(String cell) {
        String s = revertSuffix(cell);
        int n = s.lastIndexOf("$");
        if (n < 0)
            return -1;

        String num = cell.substring(n + 1);
        if (!num.matches("\\d+"))
            return -1;

        return Integer.parseInt(num);
    }

    public static String getName(String cell) {
        String s = revertSuffix(cell);
        int n = s.lastIndexOf("$");
        if (n < 0)
            return cell;

        return cell.substring(0, n);
    }

    public static String toScriptedString(String atom) {
        return toScriptedString(atom, null);
    }

    public static String toScriptedString(String atom, Set<String> multiple) {

        if (AlloyCore.isWindows())
            return atom;

        if (atom.matches(".*\\$\\d+")) {
            StringBuilder sb = new StringBuilder();
            int n = atom.lastIndexOf("$");
            String prefix = atom.substring(0, n);
            sb.append(prefix);
            for (int i = n + 1; i < atom.length(); i++) {
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

    /**
     * Turn a super scripted name back
     *
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

    /**
     * Format a solution to a string
     *
     * @param solution
     * @param instance
     * @param sigs
     * @param skolems
     * @param state
     */
    // [electrum] added state to print, -1 for static
    public static Map<String,Table> toTable(A4Solution solution, Instance instance, SafeList<Sig> sigs, SafeList<ExprVar> skolems, int state) {

        Map<String,Table> map = new TreeMap<String,Table>(new Comparator<String>() {

            @Override
            public int compare(String o1, String o2) {
                if (o1.charAt(0) == '$' && o2.charAt(0) != '$')
                    return 1;
                else if (o2.charAt(0) == '$' && o1.charAt(0) != '$')
                    return -1;
                return o1.compareTo(o2);
            }

        });

        for (Sig s : sigs) {

            if (s.builtin)
                continue;

            TupleSet instanceTuples = solution.eval(s, state).debugGetKodkodTupleset();
            if (instanceTuples != null) {

                List<SimTuple> instancesArray = Util.toList(instanceTuples);
                sortTuple(instancesArray);

                SimTupleset sigInstances = SimTupleset.make(instancesArray);
                Table table = new Table(sigInstances.size() + 1, s.getFields().size() + 1, 1);
                table.set(0, 0, s.label);

                if (s.getFields().size() == 0 && sigInstances.size() < 1)
                    continue;

                int c = 1;
                for (Field f : s.getFields()) {
                    table.set(0, c++, f.label);
                }

                map.put(s.label, table);
                int r = 1;
                for (SimTuple sigInstance : sigInstances) {
                    assert sigInstance.arity() == 1;
                    SimTupleset leftJoin = SimTupleset.make(sigInstance);

                    table.set(r, 0, sigInstance.get(0));
                    c = 1;
                    for (Field f : s.getFields()) {

                        SimTupleset relations = Util.toSimTupleset(solution.eval(f, state));
                        SimTupleset joined = leftJoin.join(relations);

                        Table relationTable = toTable(joined);
                        table.set(r, c++, relationTable);
                    }
                    r++;
                }
            }
        }

        for (ExprVar s : skolems) {
            TupleSet instanceTuples = ((A4TupleSet) solution.eval(s, state)).debugGetKodkodTupleset();
            if (instanceTuples != null) {

                List<SimTuple> instancesArray = Util.toList(instanceTuples);
                sortTuple(instancesArray);

                SimTupleset sigInstances = SimTupleset.make(instancesArray);
                Table table = new Table(2, 1, 1);
                table.set(0, 0, s.label);
                map.put(s.label, table);
                table.set(1, 0, toTable(sigInstances));

            }
        }
        return map;
    }

    static private void sortTuple(List<SimTuple> instancesArray) {
        Collections.sort(instancesArray, new Comparator<SimTuple>() {

            @Override
            public int compare(SimTuple simTuple1, SimTuple simTuple2) {
                String[] coll1 = simTuple1.get(0).toString().split("\\$");
                String[] coll2 = simTuple2.get(0).toString().split("\\$");
                if (!coll1[0].equals(coll2[0]))
                    return coll1[0].compareTo(coll2[0]);
                if (coll1.length == 2 && coll2.length == 2) {
                    try {
                        return Integer.parseInt(coll1[1]) - Integer.parseInt(coll2[1]);
                    } catch (NumberFormatException e) {
                        return 0;
                    }
                }
                return 0;
            }
        });
    }

    // public static Table toTable(SimTupleset tupleset) {
    // Table table = new Table(tupleset.size(), tupleset.arity(), 0);
    // int row = 0;
    // for ( SimTuple tuple : tupleset) {
    // int column = 0;
    // for ( SimAtom atom : tuple) {
    // table.set(row, column++, atom);
    // }
    // row++;
    // }
    //
    // return table;
    // }
    public static Table toTable(SimTupleset tupleset) {

        if (tupleset.arity() == 0) {
            return new Table(0, 0, 0);
        }

        if (tupleset.arity() == 1) {
            Table t = new Table(tupleset.size(), 1, 0);
            int row = 0;
            for (SimTuple tuple : tupleset) {
                t.set(row, 0, tuple.get(0));
                row++;
            }
            return t;
        }

        SimTupleset head = tupleset.head(1);

        Table table = new Table(head.size(), 2, 0);
        int row = 0;

        for (SimTuple tuple : head) {
            SimAtom atom = tuple.head();
            SimTuple target = SimTuple.make(atom);
            SimTupleset singleton = SimTupleset.make(target);

            SimTupleset joined = singleton.join(tupleset);

            table.set(row, 0, atom.toString());
            Table sub = toTable(joined);
            table.set(row, 1, sub);

            row++;
        }

        return table;
    }

    public static Table toTable(Type type) {
        return toTable(Util.tailThis(type.toString()), false);
    }

}
