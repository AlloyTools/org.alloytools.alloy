package org.alloytools.util.table;

import java.io.IOException;

public class HTML {

    public static String format(Table table) {

        try {
            StringBuilder sb = new StringBuilder();
            format(sb, table);
            return sb.toString();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }

    }

    private static void format(Appendable sb, Table table) throws IOException {
        sb.append("<table>\n");

        int row = 0;
        if (table.headers > 0) {
            sb.append("<thead>\n");
            while (row < table.headers) {
                formatHead(sb, table.row(row));
            }
            sb.append("</thead>\n");
        }

        sb.append("</table>\n");
    }

    private static void formatHead(Appendable sb, Cell[] row) throws IOException {
        sb.append("<tr>\n");
        for (int c = 0; c < row.length; c++) {
            sb.append("<th>");
            format(sb, row[c]);
            sb.append("</th>/n");
        }
        sb.append("</tr>\n");
    }

    private static void format(Appendable sb, Cell cell) throws IOException {
        if (cell instanceof Table) {
            format(sb, (Table) cell);
        } else {
            sb.append(cell.toString());
        }
    }

}
