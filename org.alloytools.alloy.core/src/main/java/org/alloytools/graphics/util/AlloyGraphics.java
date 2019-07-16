package org.alloytools.graphics.util;

import java.awt.Font;
import java.awt.GraphicsEnvironment;
import java.util.HashMap;
import java.util.Map;

/**
 * A central class for general graphic support functions in Alloy that have no
 * good other place
 */

public class AlloyGraphics {

    private static final Map<String,String> availableFontNames = new HashMap<String,String>();

    /**
     * The fontNames can contain a comma separated list of font names. This function
     * will parse that list trying to match the first font name that can be found in
     * the list against the list of available font families. Spaces around font
     * names are stripped. For example:
     *
     * <pre>
     *   'Input Mono, Lucinda Sans Mono, Courier New, Courier, monofont'
     * </pre>
     * <p>
     * A special case is when a font name starts with a $, in that case the name is
     * looked up in the System properties. .
     * <p>
     * If none of the names can be found, the last font is returned as a desperate
     * last attempt.
     *
     * @param fontNames comma separated list of font names
     **/

    public static synchronized String matchBestFontName(String fontNames) {
        String[] names = fontNames.trim().split("\\s*,\\s*");
        if (availableFontNames.isEmpty()) {

            GraphicsEnvironment ge = GraphicsEnvironment.getLocalGraphicsEnvironment();
            String[] availableFontFamilyNames = ge.getAvailableFontFamilyNames();
            for (String availableName : availableFontFamilyNames) {
                availableFontNames.put(toSoundex(availableName), availableName);
            }
        }
        for (String name : names) {
            if (name.startsWith("$")) {
                name = name.substring(1);
                Font font = Font.getFont(name);
                if (font != null)
                    return font.getFontName();
            } else {
                String soundex = toSoundex(name);
                String fontName = availableFontNames.get(soundex);
                if (fontName != null)
                    return name;
            }
        }
        return names[names.length - 1];
    }

    private static String toSoundex(String name) {
        StringBuilder sb = new StringBuilder(name);
        for (int i = 0; i < sb.length(); i++) {
            char c = sb.charAt(i);
            switch (c) {
                case ' ' :
                case '.' :
                case '-' :
                case '\t' :
                    sb.delete(i, i + 1);
                    i--;
                    break;
                default :
                    c = Character.toLowerCase(c);
                    sb.setCharAt(i, c);
                    break;
            }
        }
        return sb.toString();
    }


}
