package org.alloytools.util.table;

import edu.mit.csail.sdg.alloy4.TableView;

public class StringCell implements Cell {

    public final String[] value;
    public final int      width;

    public StringCell(String label) {
        this.value = label.trim().split("\\s*\r?\n\\s*");
        for (int i = 0; i < value.length; i++) {
            this.value[i] = TableView.toScriptedString(this.value[i]);
        }
        int w = 0;
        for (String l : value) {
            if (l.length() > w)
                w = l.length();
        }
        this.width = w;
    }

    @Override
    public int width() {
        return width + 2;
    }

    @Override
    public int height() {
        return value.length + 2;
    }

    @Override
    public String toString() {
        return String.join("\n", value);
    }


}
