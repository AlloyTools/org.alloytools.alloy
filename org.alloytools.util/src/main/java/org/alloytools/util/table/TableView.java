package org.alloytools.util.table;

import java.util.Map;
import java.util.Map.Entry;
import java.util.TreeMap;
import java.util.regex.Pattern;

import org.alloytools.alloy.core.api.IAtom;
import org.alloytools.alloy.core.api.IRelation;
import org.alloytools.alloy.core.api.ITuple;
import org.alloytools.alloy.core.api.Instance;
import org.alloytools.alloy.core.api.Module;
import org.alloytools.alloy.core.api.Solution;
import org.alloytools.alloy.core.api.TSignature;

/**
 *
 * @modified [electrum] adapted to focus on particular state
 *
 */
public class TableView {

    final static String  SUPERSCRIPTS = "⁰¹²³⁴⁵⁶⁷⁸⁹";
    final static String  SUBSCRIPTS   = "₀₁₂₃₄₅₆₇₈₉";
    final static String  BOX_SINGLE   = "│┌─┬┐┘┴└├┼┤";
    final static Pattern TABLE_P      = Pattern.compile("\\s*\\{(([\\d\\w$\\s,>\"-]+))\\}\\s*");


    /**
     * Format a solution to a string
     */
    public static Map<String,Table> toTable(Solution solution, Instance instance) {
        Module module = solution.getModule();

        Map<String,Table> map = new TreeMap<String,Table>();

        for (TSignature sig : module.getSignatures().values()) {
            IRelation atoms = instance.getAtoms(sig);
            if (atoms.isEmpty())
                continue;


            if (sig.getFieldMap().isEmpty()) {
                map.put(sig.getName(), toTable(atoms));
            } else {

                map.put(sig.getName(), doObjectTable(sig, atoms, instance));
            }
        }

        for (Entry<String,IRelation> e : instance.getVariables().entrySet()) {
            map.put(e.getKey(), toTable(e.getValue()));
        }
        return map;
    }

    private static Table doObjectTable(TSignature sig, IRelation atoms, Instance instance) {
        // TODO Auto-generated method stub
        return null;
    }

    private static Table doHorizontalTable(IRelation atoms) {
        // TODO Auto-generated method stub
        return null;
    }

    public static Table toTable(IRelation tupleset) {

        if (tupleset.arity() == 0) {
            Table table = new Table(1, 1, 0);
            if (tupleset.getSolution().none() == tupleset)
                table.set(0, 0, "none");
            else if (tupleset.getSolution().error() == tupleset)
                table.set(0, 0, "error");
            else
                table.set(0, 0, "?");
            return table;
        }

        if (tupleset.arity() == 1) {
            Table t = new Table(tupleset.size(), 1, 0);
            int row = 0;
            for (ITuple tuple : tupleset) {
                t.set(row, 0, tuple.get(0));
                row++;
            }
            return t;
        }

        IRelation head = tupleset.head();

        Table table = new Table(head.size(), 2, 0);
        int row = 0;

        for (ITuple tuple : head) {
            IAtom atom = tuple.first();
            IRelation singleton = atom.asTupleSet();

            IRelation joined = singleton.join(tupleset);

            table.set(row, 0, atom.toString());
            Table sub = toTable(joined);
            table.set(row, 1, sub);

            row++;
        }

        return table;
    }

}
