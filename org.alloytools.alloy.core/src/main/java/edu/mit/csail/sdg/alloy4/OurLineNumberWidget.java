package edu.mit.csail.sdg.alloy4;

import javax.swing.*;
import javax.swing.event.CaretEvent;
import javax.swing.event.CaretListener;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.text.BadLocationException;
import javax.swing.text.Element;
import javax.swing.text.Utilities;
import java.awt.*;
import java.awt.event.ComponentEvent;
import java.awt.event.ComponentListener;
import java.awt.font.FontRenderContext;
import java.util.Collections;
import java.util.Objects;

public class OurLineNumberWidget extends JComponent implements DocumentListener, CaretListener, ComponentListener {

    /**
     * combine the two submitted objects with a new OurLineNumberWidget and return
     * that widget.  We assume that other code has already connected these components appropriately.
     *
     * While callers could send any fontName and size that they wanted, here in Allow in the context of
     * the editor the assumption is that the font preference set by the user for the whole app is
     * applying here as well, so OurSyntaxWidget will be sending the same font that it receives to use.
     *
     * @param textPane the text pane that has the lines we want to draw numbers for
     * @param scrollPane the scroll pane we will set a header row for to draw the line numbers for textPane
     * @param display line numbers should display if true, should not otherwise
     * @param fontName the fontName to be used to draw line numbers.
     * @return the OurLineNumberWidget linking  the two components, with the display and font set.
     */
    public static OurLineNumberWidget build(JTextPane textPane, JScrollPane scrollPane, boolean display, String fontName, int fontSize) {
        Objects.requireNonNull(textPane);
        Objects.requireNonNull(textPane.getDocument());
        Objects.requireNonNull(scrollPane);
        Objects.requireNonNull(fontName);
        if ( fontSize < 1 ) {
            throw new IllegalArgumentException("Font size must be at least 1");
        }

        OurLineNumberWidget ourLineNumberWidget = new OurLineNumberWidget(textPane, display, fontName, fontSize);
        scrollPane.setRowHeaderView(ourLineNumberWidget);
        return ourLineNumberWidget;
    }

    private static final boolean antiAlias = Util.onMac() || Util.onWindows();

    private final JTextPane textPane;
    private boolean display;
    private String fontName;
    private int fontSize;
    private int width = 0;
    private Font font;
    /** assume we start showing 1 digit. */
    private int currentMaxDigits = 1;
    private int descentAdjust;

    OurLineNumberWidget(JTextPane textPane, boolean display, String fontName, int fontSize) {
        this.textPane = textPane;
        this.display = display;
        this.fontName = fontName;
        this.fontSize = fontSize;

        // falls back to 'Dialog' on not being able to find.
        this.font = new Font(this.fontName, Font.PLAIN, this.fontSize);
        this.descentAdjust = makeDescentAdjust();

        textPane.getDocument().addDocumentListener(this);
        textPane.addComponentListener(this);
        textPane.addCaretListener(this);

        update();
    }

    /** use current font to decide a width for the line-number view itself,
     * based on how many digits are submitted.
     * @param numberOfDigits
     * @return
     */
    private int calculateWidthForDigits(int numberOfDigits) {
        if ( display ) {
            String numberOfDigitsLong = String.join("", Collections.nCopies(numberOfDigits, "0"));
            return (int)Math.ceil(
                    font.getStringBounds(numberOfDigitsLong, new FontRenderContext(null, false, false)).getWidth() * 1.2);
        } else {
            return 0;
        }
    }

    /** capture the descent of the current font, used to adjust (negative y) where the
     * line number is drawn.  Only needs to change when the font changes.
     * @return
     */
    private int makeDescentAdjust() {
        return getFontMetrics(font).getDescent();
    }

    @Override
    protected void paintComponent(final Graphics g) {

        if ( ! display ) { return; }

        if ( g instanceof Graphics2D && antiAlias ) {
            ((Graphics2D)g).setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
        }

        super.paintComponent(g);
        // antiAlias at some point

        Rectangle bounds = g.getClipBounds();
        final int startDocumentLocation = textPane.viewToModel(new Point(0, bounds.y));
        final int endDocumentLocation = textPane.viewToModel(new Point(0, bounds.y + bounds.height));

        int docLoc = startDocumentLocation;
        int maxDigits = 0;

        while ( docLoc <= endDocumentLocation ) {
            try {
                Element rootElement = textPane.getDocument().getDefaultRootElement();
                final int lineIndex = rootElement.getElementIndex(docLoc);
                final Element line = rootElement.getElement(lineIndex);
                if (line.getStartOffset() == docLoc) {
                    int x = niceX();
                    int y = niceY(docLoc);

                    String formattedLineNumber = formatLineNumberFromIndex(lineIndex);
                    if ( formattedLineNumber.length() > maxDigits ) {
                        maxDigits = formattedLineNumber.length();
                    }

                    g.setColor(Color.BLACK);
                    if (ifCaretOnSameLine(docLoc, rootElement)) {
                        Rectangle currentLineViewRec = textPane.modelToView(docLoc);
                        g.fillRect(0, currentLineViewRec.y, width, currentLineViewRec.height-1 );
                        g.setColor(Color.YELLOW);
                    }
                    g.setFont(font);
                    g.drawString(formattedLineNumber, x, y);
                }
                docLoc = Utilities.getRowEnd(textPane, docLoc) + 1;
            } catch (BadLocationException e) {
                // what is the right thing to do here?
            }
        }
        if ( maxDigits != currentMaxDigits ) {
            currentMaxDigits = maxDigits;
            update();
        }
    }

    private boolean ifCaretOnSameLine(int docLoc, Element rootElement) {
        return rootElement.getElementIndex(docLoc) == rootElement.getElementIndex(textPane.getCaretPosition());
    }

    /** a judgement about where in the x direction is good
     * to start drawing the line number.
     * @return
     */
    private int niceX() {
        return getInsets().left + 3;
    }

    /** a judgement about where in the y direction is good
     * to start drawing the line number for the given document location.
     * @param docLoc
     * @return
     * @throws BadLocationException
     */
    private int niceY(int docLoc) throws BadLocationException {
        Rectangle viewRec = textPane.modelToView(docLoc);
        return viewRec.y + viewRec.height - descentAdjust;
    }

    private String formatLineNumberFromIndex(int lineIndex) {
        return String.format("%d", (lineIndex + 1));
    }

    /** Make a new width value, set new current preferred size and size,
     * and try to get this component repainted.
     * Currently all listener events incur this, which might be more
     * than strictly needed.
     */
    private void update() {
        width = calculateWidthForDigits(currentMaxDigits);
        Dimension size = new Dimension(width, textPane.getHeight());
        setPreferredSize(size);
        setSize(size);
        SwingUtilities.invokeLater(this::repaint);
    }

    // component listener events
    @Override
    public void componentResized(ComponentEvent e) {
        update();
    }

    @Override
    public void componentMoved(ComponentEvent e) {
        update();
    }

    @Override
    public void componentShown(ComponentEvent e) {
        update();
    }

    @Override
    public void componentHidden(ComponentEvent e) {
        update();
    }

    // caret listener events
    @Override
    public void caretUpdate(CaretEvent e) {
        update();
    }

    // document listener events
    @Override
    public void insertUpdate(DocumentEvent e) {
        update();
    }

    @Override
    public void removeUpdate(DocumentEvent e) {
        update();
    }

    @Override
    public void changedUpdate(DocumentEvent e) {
        update();
    }

    /**
     * Set whether this widget should display or not display line numbers,
     * incur an update() call if there is a change.
     * @param flag
     */
    public void setDisplay(boolean flag) {
        boolean oldDisplay = display;
        this.display = flag;
        if ( this.display != oldDisplay ) {
            update();
        }
    }

    /**
     * Set the fontName and fontSize for this widget.  If the
     * submitted name and size amount to a change of the font itself,
     * incur an update() call.
     * @param fontName
     * @param fontSize
     */
    public void updateFontNameAndSize(String fontName, int fontSize) {
        if ( fontSize < 1 ) {
            if ( fontName == null || fontName.isEmpty() ) {
                fontName = Font.MONOSPACED;
            }
            fontSize = 14;
        }
        String oldFontName = this.fontName;
        int oldFontSize = this.fontSize;

        this.fontName = fontName;
        this.fontSize = fontSize;

        if ( !this.fontName.equals(oldFontName) || this.fontSize != oldFontSize ) {
            font = new Font(this.fontName, Font.PLAIN, this.fontSize);
            descentAdjust = makeDescentAdjust();
            update();
        }
    }


}
