package org.alloytools.util.table;

public class Table implements Cell {

    public final int         rows;
    public final int         cols;
    public final Cell[][]    cells;
    final public int         headers;
    Canvas.Style             style = Canvas.PLAIN;

    public static final Cell EMPTY = new Cell() {

                                       @Override
                                       public int width() {
                                           return 3;
                                       }

                                       @Override
                                       public int height() {
                                           return 3;
                                       }

                                       @Override
                                       public String toString() {
                                           return " ";
                                       }
                                   };

    public Table(int rows, int cols, int headers) {
        this.rows = rows;
        this.cols = cols;
        this.headers = headers;
        cells = new Cell[rows][cols];
        for (int r = 0; r < rows; r++) {
            for (int c = 0; c < cols; c++) {
                cells[r][c] = EMPTY;
            }
        }
    }

    /**
     * Width including borders
     */
    @Override
    public int width() {
        int w = 0;
        for (int c = 0; c < cols; c++) {
            w += width(c) - 1; // remove right border width because we overlap
        }
        return w + 1; // add right border
    }

    /**
     * Height including borders
     */
    @Override
    public int height() {
        int h = 0;
        for (int r = 0; r < rows; r++) {
            h += height(r) - 1;// remove bottom border width because we overlap
        }
        return h + 1; // add bottom border
    }

    public void set(int r, int c, Object label) {
        cells[r][c] = new StringCell("" + label);
    }

    public void set(int r, int c, Cell table) {
        cells[r][c] = table;
    }

    public Cell[] row(int row) {
        return cells[row];
    }

    @Override
    public String toString() {
        if (cols == 1 && rows > 3)
            return transpose(0).toString("⁻¹");
        else
            return toString(null);
    }

    @Override
    public Canvas render(int width, int height) {
        return render(width, height, 0, 0, 0, 0);
    }

    public Canvas render(int width, int height, int left, int top, int right, int bottom) {

        Canvas canvas = new Canvas(width + left + right, height + top + bottom);
        canvas.box(left, top, width, height, style);

        int y = top;

        for (int r = 0; r < rows; r++) {
            int ch = height(r);
            int x = left;
            for (int c = 0; c < cols; c++) {
                int cw;
                if (c == cols - 1) {
                    // adjust last column width
                    cw = width - x - left;
                } else {
                    cw = width(c);
                }
                Cell cell = cells[r][c];
                Canvas foo = cell.render(cw, ch);
                canvas.merge(foo, x, y);
                x += cw - 1;
            }
            y += ch - 1;
        }
        return canvas;
    }

    /**
     * Width of a column without borders
     *
     * @param col
     * @return
     */
    private int width(int col) {
        int w = 0;
        for (int r = 0; r < rows; r++) {
            Cell cell = cells[r][col];
            int width = cell.width();
            if (width > w)
                w = width;
        }
        return w;
    }

    public int height(int row) {
        int h = 0;
        for (int c = 0; c < cols; c++) {
            Cell cell = cells[row][c];
            int height = cell.height();
            if (height > h)
                h = height;
        }
        return h;
    }

    public Table transpose(int headers) {
        Table transposed = new Table(cols, rows, headers);
        for (int row = 0; row < rows; row++) {
            for (int col = 0; col < cols; col++) {
                Cell c = this.get(row, col);
                transposed.set(col, row, c);
            }
        }
        return transposed;
    }

    public Cell get(int row, int col) {
        return cells[row][col];
    }

    public String toString(String message) {
        if (message == null)
            message = "";

        if (rows == 0 || cols == 0) {
            return "☒" + message;
        }
        Canvas render = render(width(), height(), 0, 0, message.length(), 0);
        render.set(width(), 0, message);
        return render.toString();
    }

    public Table addColum(int col) {
        Table t = new Table(rows, cols + 1, headers);
        if (col > 0)
            copy(t, 0, 0, 0, 0, rows, col);

        return copy(t, 0, col, 0, col + 1, rows, cols - col);
    }

    public Table setColumn(int col, Object cell) {
        for (int r = 0; r < rows; r++)
            set(r, col, cell);

        return this;
    }

    public Table copy(Table t, int sourceRow, int sourceCol, int destRow, int destCol, int rows, int cols) {
        for (int i = 0; i < rows; i++) {
            for (int j = 0; i < cols; i++) {
                Cell cell = get(sourceRow + i, sourceCol + j);
                t.set(destRow + i, destCol + j, cell);
            }
        }
        return t;
    }

    public void setBold() {
        style = Canvas.BOLD;
    }

}
