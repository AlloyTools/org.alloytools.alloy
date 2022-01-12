package edu.mit.csail.sdg.alloy4;

import org.junit.Test;

import javax.swing.border.EmptyBorder;
import javax.swing.text.JTextComponent;
import java.awt.*;
import java.awt.font.FontRenderContext;

import static org.junit.Assert.*;

/**
 * Test the logic of the LineNumbersView as best we can.
 */
public class LineNumbersViewTest {

    JTextComponent dummyTextComponent = OurAntiAlias.pane(null, Color.BLACK, Color.WHITE, new EmptyBorder(6, 6, 6, 6));

    @Test
    public void some_font_always_set_after_construction() throws Exception {
        LineNumbersView lineNumbersView;

        lineNumbersView = new LineNumbersView(dummyTextComponent, true, Font.MONOSPACED, 15);
        assertNotNull(lineNumbersView.getFont());
        assertEquals("Monospaced", lineNumbersView.getFontName());
        assertEquals(15, lineNumbersView.getFontSize());

        lineNumbersView = new LineNumbersView(dummyTextComponent, true, null, 15);
        assertNotNull(lineNumbersView.getFont());
        assertEquals("Monospaced", lineNumbersView.getFontName());
        assertEquals(14, lineNumbersView.getFontSize());

        lineNumbersView = new LineNumbersView(dummyTextComponent, true, null, -3);
        assertNotNull(lineNumbersView.getFont());
        assertEquals("Monospaced", lineNumbersView.getFontName());
        assertEquals(14, lineNumbersView.getFontSize());

        lineNumbersView = new LineNumbersView(dummyTextComponent, true, Font.DIALOG, -3);
        assertNotNull(lineNumbersView.getFont());
        assertEquals("Monospaced", lineNumbersView.getFontName());
        assertEquals(14, lineNumbersView.getFontSize());

        lineNumbersView = new LineNumbersView(dummyTextComponent, true, Font.DIALOG, 17);
        assertNotNull(lineNumbersView.getFont());
        assertEquals("Dialog", lineNumbersView.getFontName());
        assertEquals(17, lineNumbersView.getFontSize());
    }

    @Test
    public void antialias_set_correctly() throws Exception {

        String originalOs = System.getProperty("os.name", "UNKNOWN");
        LineNumbersView lineNumbersView;

        System.setProperty("os.name", "Windows27");
        lineNumbersView = new LineNumbersView(dummyTextComponent, true, "Monospaced", 15);
        assertTrue(lineNumbersView.isAntiAlias());

        System.setProperty("os.name", "Mac 100");
        lineNumbersView = new LineNumbersView(dummyTextComponent, true, "Monospaced", 15);
        assertTrue(lineNumbersView.isAntiAlias());

        System.setProperty("os.name", "linux 2049");
        lineNumbersView = new LineNumbersView(dummyTextComponent, true, "Monospaced", 15);
        assertFalse(lineNumbersView.isAntiAlias());

        System.setProperty("os.name", "Belchfire Status Symbol X100");
        lineNumbersView = new LineNumbersView(dummyTextComponent, true, "Monospaced", 15);
        assertFalse(lineNumbersView.isAntiAlias());

        System.setProperty("os.name", originalOs);
    }

    @Test
    public void requires_editor_not_null() throws Exception {
        try {
            LineNumbersView lineNumbersView = new LineNumbersView(null, true, "Monospaced", 15);
            fail("should have not constructed with null editor parameter");
        } catch (Throwable t) {

        }
    }

    @Test
    public void margin_width_calculated_reasonably() throws Exception {
        LineNumbersView lineNumbersView = new LineNumbersView(dummyTextComponent, true, "Monospaced", 15);
        Font monospaced15Font = new Font("Monospaced", Font.PLAIN, 15);
        int expected = (int)Math.ceil(monospaced15Font
                .getStringBounds("000", new FontRenderContext(null, true, false))
                .getWidth() * 1.1);

        assertEquals(
            expected,
                lineNumbersView.calculateMarginWidth()
        );
    }

}
