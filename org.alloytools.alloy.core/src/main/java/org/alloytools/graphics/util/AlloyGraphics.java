package org.alloytools.graphics.util;

import java.awt.Font;
import java.awt.GraphicsEnvironment;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

public class AlloyGraphics {

    private static Set<String> availableFontNames;

    public static synchronized String matchBestFontName(String fontName) {
        String[] names = fontName.trim().split("\\s*,\\s*");
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
