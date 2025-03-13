package org.alloytools.graphics.util;

import java.awt.Font;
import java.awt.FontMetrics;
import java.awt.GraphicsEnvironment;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import javax.swing.JLabel;

/**
 * A central class for general graphic support functions in Alloy that have no
 * good other place
 */

public class AlloyGraphics {

    final static String                      TEST_S             = "abcdefghijklmnoqpqrstuvwxyz1234567890ABCDEFGHIJKLMNOPQRSTUVWXYZ!@#$%^&*()_+=-{}[]|\"':;<>.,?/~`";

    static final List<FontFamilyDescription> availableFontNames = new ArrayList<>();

    record FontFamilyDescription(boolean monospace, String name, String soundex) {
    }

    /**
     * Answer if a font family is mono space. This defined as having the same widths
     * for the test alfabet and important punctuation and the capability to display
     * these characters.
     *
     * @param fontFamilyName the font family
     * @return true if mono space
     */
    public static boolean isMono(String fontFamilyName) {
        Optional<FontFamilyDescription> any = getAvailableFontDescriptions().stream().filter(ffd -> ffd.monospace && ffd.name().equals(fontFamilyName)).findAny();
        return any.isPresent();
    }


    /**
     * Get a list of all available family names.
     *
     * @param all show all fonts, otherwise only fonts deemed monospaced
     */
    public static List<String> getFontFamilyNames(boolean all) {
        return getAvailableFontDescriptions().stream().filter(ffd -> all || ffd.monospace).map(ffd -> ffd.name).toList();
    }

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
        List<FontFamilyDescription> availableFontNames = getAvailableFontDescriptions();
        String[] names = fontNames.trim().split("\\s*,\\s*");

        for (String name : names) {
            String target = name.startsWith("$") ? name.substring(1) : name;
            Optional<FontFamilyDescription> fontName = availableFontNames.stream().filter(ffd -> ffd.name().equals(target)).findFirst();
            if (fontName.isPresent())
                return fontName.get().name;
        }

        for (String name : names) {
            String soundex = toSoundex(name);
            Optional<FontFamilyDescription> fontName = availableFontNames.stream().filter(ffd -> ffd.soundex().equals(soundex)).findFirst();
            if (fontName.isPresent())
                return fontName.get().name;
        }
        return Font.MONOSPACED;
    }

    private static List<FontFamilyDescription> getAvailableFontDescriptions() {
        if (availableFontNames.isEmpty()) {
            JLabel label = new JLabel();
            GraphicsEnvironment ge = GraphicsEnvironment.getLocalGraphicsEnvironment();
            Font[] allFonts = ge.getAllFonts();
            Set<String> set = new HashSet<>();
            set.add(Font.MONOSPACED);
            availableFontNames.add(new FontFamilyDescription(true, Font.MONOSPACED, toSoundex(Font.MONOSPACED)));

            for (Font font : allFonts) {
                String familyName = font.getFamily();
                if (!set.add(familyName))
                    continue;

                boolean monospace = true;
                if (font.isBold() || font.isItalic())
                    monospace = false;

                if (font.canDisplayUpTo(TEST_S) != -1)
                    monospace = false;

                String soundex = toSoundex(familyName);


                FontMetrics metrics = label.getFontMetrics(font);
                double w = metrics.stringWidth(TEST_S);
                if (w == 0 || w / TEST_S.length() != 1)
                    monospace = false;

                availableFontNames.add(new FontFamilyDescription(monospace, familyName, soundex));
            }
        }
        return availableFontNames;
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
