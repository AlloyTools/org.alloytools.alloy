package org.alloytools.graphics.util;

import java.awt.Font;
import java.awt.GraphicsEnvironment;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

/**
 * A central class for general graphic support functions in Alloy that have no good other 
 * place
 */

public class AlloyGraphics {

    private static Set<String> availableFontNames;

    /**
     * The fontNames can contain a comma separated list of font names. This
     * function will parse that list trying to match the first font name that
     * can be found in the list against the list of available font families. 
     * Spaces around font names are stripped. For example:
     * <pre>
     *   'Input Mono, Lucinda Sans Mono, Courier New, Courier, monofont' 
     * </pre>
     *<p>
     * A special case is when a font name starts with a $, in that case the
     * name is looked up in the System properties. {@see Font#getFont(String)}.
     * <p>
     * If none of the names can be found, the last font is returned as
     * a desperate last attempt.
     *
     * @param fontNames comma separated list of font names
     **/
    
    public static synchronized String matchBestFontName(String fontNames) {
        String[] names = fontNames.trim().split("\\s*,\\s*");
        if (availableFontNames == null) {
            GraphicsEnvironment ge = GraphicsEnvironment.getLocalGraphicsEnvironment();
            availableFontNames = new HashSet<>(Arrays.asList(ge.getAvailableFontFamilyNames()));
        }
        for (String name : names) {
            if (name.startsWith("$")) {
                name = name.substring(1);
                Font font = Font.getFont(name);
                if (font != null)
                    return font.getFontName();
            } else {
                if (availableFontNames.contains(name))
                    return name;
            }
        }
        return names[names.length - 1];
    }


}
