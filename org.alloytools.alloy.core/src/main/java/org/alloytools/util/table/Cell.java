package org.alloytools.util.table;

public interface Cell {

    /**
     * Width including its borders on left and right
     */
    int width();

    /**
     * Height including its borders on top and bottom
     */
    int height();

    /**
     * Render including borders
     *
     * @param w
     * @param h
     * @return
     */
    default Canvas render(int w, int h) {
        Canvas canvas = new Canvas(w, h);
        canvas.box();
        String[] lines = this.toString().split("\r?\n");
        for (int y = 0; y < lines.length && y < h - 2; y++) {
            for (int x = 0; x < w - 2 && x < lines[y].length(); x++) {
                canvas.set(x + 1, y + 1, lines[y].charAt(x));
            }
        }
        return canvas;
    }

}
