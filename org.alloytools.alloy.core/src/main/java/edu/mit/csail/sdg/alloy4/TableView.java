package edu.mit.csail.sdg.alloy4;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.alloytools.alloy.core.AlloyCore;
import org.alloytools.util.table.Table;

import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Type;
import edu.mit.csail.sdg.sim.SimAtom;
import edu.mit.csail.sdg.sim.SimTuple;
import edu.mit.csail.sdg.sim.SimTupleset;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.A4Tuple;
import edu.mit.csail.sdg.translator.A4TupleSet;
import kodkod.instance.Instance;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;

public class TableView {

    final static String  SUPERSCRIPTS = "⁰¹²³⁴⁵⁶⁷⁸⁹";
    final static String  SUBSCRIPTS   = "₀₁₂₃₄₅₆₇₈₉";
    final static String  BOX_SINGLE   = "│┌─┬┐┘┴└├┼┤";
    final static Pattern TABLE_P      = Pattern.compile("\\s*\\{(([\\d\\w$\\s,>\"-]+))\\}\\s*");

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

    /**
     * Format a solution to a string
     *
     * @param solution
     * @param instance
     * @param sigs
     * @return
     */
    public static Map<String,Table> toTable(A4Solution solution, Instance instance, SafeList<Sig> sigs) {

        Map<String,Table> map = new HashMap<String,Table>();

        for (Sig s : sigs) {

            if (!s.label.startsWith("this/"))
                continue;

            TupleSet instanceTuples = instance.tuples(s.label);
            if (instanceTuples != null) {

                SimTupleset sigInstances = toSimTupleset(instanceTuples);
                Table table = new Table(sigInstances.size() + 1, s.getFields().size() + 1, 1);
                table.set(0, 0, s.label);

                if (s.getFields().size() == 0 && sigInstances.size() <= 1)
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

                        SimTupleset relations = toSimTupleset(solution.eval(f));
                        SimTupleset joined = leftJoin.join(relations);

                        Table relationTable = toTable(joined);
                        table.set(r, c++, relationTable);
                    }
                    r++;
                }
            }
        }
        return map;
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

    private static SimTupleset toSimTupleset(A4TupleSet values) {
        List<SimTuple> l = new ArrayList<>();
        for (A4Tuple a4t : values) {
            l.add(toSimTuple(a4t));
        }
        return SimTupleset.make(l);
    }

    private static SimTuple toSimTuple(A4Tuple a4t) {
        List<SimAtom> atoms = new ArrayList<>();
        for (int i = 0; i < a4t.arity(); i++) {
            SimAtom atom = SimAtom.make(a4t.atom(i));
            atoms.add(atom);
        }
        return SimTuple.make(atoms);
    }

    private static SimTupleset toSimTupleset(TupleSet tupleSet) {
        List<SimTuple> l = new ArrayList<>();
        for (Tuple tuple : tupleSet) {
            l.add(toSimTuple(tuple));
        }
        return SimTupleset.make(l);
    }

    private static SimTuple toSimTuple(Tuple tuple) {
        List<SimAtom> atoms = new ArrayList<>();
        for (int i = 0; i < tuple.arity(); i++) {
            SimAtom atom = SimAtom.make(tuple.atom(i).toString());
            atoms.add(atom);
        }
        return SimTuple.make(atoms);
    }

    public static Table toTable(Type type) {
        return toTable(type.toString().replaceAll("this/", ""), false);
    }

    public static String clean(String label) {
        return label.replaceAll("this/", "");
    }

}
