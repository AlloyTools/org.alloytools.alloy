package org.alloytools.util;

import java.util.ServiceLoader;

import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.IRelation;
import org.alloytools.alloy.core.api.Instance;
import org.alloytools.alloy.core.api.Solution;
import org.alloytools.util.table.Table;
import org.alloytools.util.table.TableView;
import org.junit.Test;


public class TableViewTest {

    final Alloy alloy = ServiceLoader.load(Alloy.class).iterator().next();

    @Test
    public void testSimple() {
        Solution solution = alloy.getSolution("sig Foo{} run { #Foo = 3}");
        Instance next = solution.iterator().next();
        IRelation eval = next.eval("Foo");
        Table table = TableView.toTable(eval);
        String string = table.toString();
        System.out.println(string);
    }

}
