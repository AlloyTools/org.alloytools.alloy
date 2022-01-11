package edu.mit.csail.sdg.alloy4;

import javax.swing.*;
import javax.swing.event.CaretEvent;
import javax.swing.event.CaretListener;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.text.BadLocationException;
import javax.swing.text.Element;
import javax.swing.text.JTextComponent;
import javax.swing.text.Utilities;
import java.awt.*;
import java.awt.event.ComponentEvent;
import java.awt.event.ComponentListener;
import java.awt.font.FontRenderContext;
import java.util.Objects;

/**
 * Provides display of line-numbers to a provided JTextComponent.
 * An instance is used to populate the rowHeader property of a JScrollPane instance,
 * based on information and events from the JTextComponent instance supplied
 * at initialization.
 *
 * Uses fontName and fontSize provided at initialization time, and as updated
 * by callers.  Follows the anti-aliasing policy that {@link OurAntiAlias} follows, which
 * is not tied to user preferences.
 */

public class LineNumbersView extends JComponent implements DocumentListener, CaretListener, ComponentListener {

    private static final long serialVersionUID = 1L;

    private final JTextComponent editor;
    private final boolean antiAlias;

    private int marginWidth = 0;
    private boolean lineNumbers = false;
    private String fontName;
    private int fontSize;
    private Font font;

    public LineNumbersView(JTextComponent editor, boolean shouldDisplay, String fontName, int fontSize) {
        Objects.requireNonNull(editor, "Need a non-null JTextComponent for parameter editor");
        this.editor = editor;
        this.antiAlias = Util.onMac() || Util.onWindows();

        if ( fontName != null && fontSize > 1 ) {
            this.fontName = fontName;
            this.fontSize = fontSize;
        } else {
            this.fontName = Font.MONOSPACED;
            this.fontSize = 14;
        }
        font = new Font(fontName, Font.PLAIN, fontSize);

        this.lineNumbers = shouldDisplay;
        if ( lineNumbers ) {
            marginWidth = calculateMarginWidth();
            editor.getDocument().addDocumentListener(this);
            editor.addComponentListener(this);
            editor.addCaretListener(this);
        } else {
            marginWidth = 0;
        }
    }

    @Override
    public void paintComponent(Graphics g) {
        if (antiAlias && g instanceof Graphics2D) {
            ((Graphics2D) g).setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
        }
        super.paintComponent(g);

        if (lineNumbers) {
            font = getUpdatedFont();
            Rectangle clip = g.getClipBounds();
            int startOffset = editor.viewToModel(new Point(0, clip.y));
            int endOffset = editor.viewToModel(new Point(0, clip.y + clip.height));

            while (startOffset <= endOffset) {
                try {
                    String lineNumber = getLineNumber(startOffset);
                    if (lineNumber != null) {
                        int x = getInsets().left + 2;
                        int y = getOffsetY(startOffset);

                        g.setFont(font);
                        g.setColor(isCurrentLine(startOffset) ? Color.RED : Color.BLACK);
                        g.drawString(lineNumber, x, y);
                    }
                    startOffset = Utilities.getRowEnd(editor, startOffset) + 1;
                } catch (BadLocationException e) {
                    e.printStackTrace();
                }
            }
        }
    }

    /** update the font we will use to draw numbers from the provided editor component.  */
    private Font getUpdatedFont() {
        if ( fontName.equals(font.getFontName()) || fontSize != font.getSize()) {
            return new Font(fontName, Font.PLAIN, fontSize);
        } else {
            return font;
        }
    }

    private String getLineNumber(int offset) {
        Element root = editor.getDocument().getDefaultRootElement();
        int index = root.getElementIndex(offset);
        Element line = root.getElement(index);

        // how long are alloy specifications often?
        return line.getStartOffset() == offset ? String.format("%3d", index + 1) : null;
    }

    private int getOffsetY(int offset) throws BadLocationException {
        FontMetrics fontMetrics = editor.getFontMetrics(editor.getFont());
        int descent = fontMetrics.getDescent();

        Rectangle r = editor.modelToView(offset);
        return r.y + r.height - descent;
    }

    private boolean isCurrentLine(int offset) {
        int caretPosition = editor.getCaretPosition();
        Element root = editor.getDocument().getDefaultRootElement();
        return root.getElementIndex(offset) == root.getElementIndex(caretPosition);
    }

    private void documentChanged() {
        SwingUtilities.invokeLater(() -> {
            repaint();
        });
    }

    private void updateSize() {
        Dimension size = new Dimension(marginWidth, editor.getHeight());
        setPreferredSize(size);
        setSize(size);
    }

    @Override
    public void insertUpdate(DocumentEvent e) {
        documentChanged();
    }

    @Override
    public void removeUpdate(DocumentEvent e) {
        documentChanged();
    }

    @Override
    public void changedUpdate(DocumentEvent e) {
        documentChanged();
    }

    @Override
    public void caretUpdate(CaretEvent e) {
        documentChanged();
    }

    @Override
    public void componentResized(ComponentEvent e) {
        updateSize();
        documentChanged();
    }

    @Override
    public void componentMoved(ComponentEvent e) {
    }

    @Override
    public void componentShown(ComponentEvent e) {
        updateSize();
        documentChanged();
    }

    @Override
    public void componentHidden(ComponentEvent e) {
    }

    public void updateFontNameAndFontSize(String fontName, int fontSize) {
        this.fontName = fontName;
        this.fontSize = fontSize;
        font = getUpdatedFont();
        updateSize();
        documentChanged();
    }

    public void enableLineNumbers(boolean flag) {
        lineNumbers = flag;
        if (lineNumbers) {
            marginWidth = calculateMarginWidth();
            editor.getDocument().addDocumentListener(this);
            editor.addComponentListener(this);
            editor.addCaretListener(this);
        } else {
            marginWidth = 0;
        }
        font = getUpdatedFont();
        updateSize();
        documentChanged();
    }

    /** produce a width in pixels for this margin when it is to be drawn.
     * make an effort to have our page-number margin only wide enough for three numerals, no wider. */
    private int calculateMarginWidth() {
        if ( font != null ) {
            return (int) Math.ceil(font
                    .getStringBounds("000", new FontRenderContext(null, antiAlias, false))
                    .getWidth() * 1.1);
        } else {
            return fontSize * 2;
        }

    }
}