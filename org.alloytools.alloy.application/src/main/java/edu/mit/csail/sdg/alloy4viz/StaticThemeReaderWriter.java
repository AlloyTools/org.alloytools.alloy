/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.alloy4viz;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4.XMLNode;
import edu.mit.csail.sdg.alloy4graph.DotColor;
import edu.mit.csail.sdg.alloy4graph.DotPalette;
import edu.mit.csail.sdg.alloy4graph.DotShape;
import edu.mit.csail.sdg.alloy4graph.DotStyle;

/**
 * This utility class contains methods to read and write VizState
 * customizations.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

public final class StaticThemeReaderWriter {

    /**
     * Constructor is private, since this utility class never needs to be
     * instantiated.
     */
    private StaticThemeReaderWriter() {}

    /**
     * Read the XML file and merge its settings into an existing VizState object.
     */
    public static void readAlloy(String filename, VizState theme) throws IOException {
        File file = new File(filename);
        try {
            XMLNode elem = new XMLNode(file);
            for (XMLNode sub : elem.getChildren("view"))
                parseView(sub, theme);
        } catch (Throwable e) {
            throw new IOException("The file \"" + file.getPath() + "\" is not a valid XML file, or an error occurred in reading.");
        }
    }

    /**
     * Write the VizState's customizations into a new file (which will be
     * overwritten if it exists).
     */
    public static void writeAlloy(String filename, VizState theme) throws IOException {
        PrintWriter bw = new PrintWriter(filename, "UTF-8");
        bw.write("<?xml version=\"1.0\"?>\n<alloy>\n\n");
        if (theme != null) {
            try {
                writeView(bw, theme);
            } catch (IOException ex) {
                Util.close(bw);
                throw new IOException("Error writing to the file \"" + filename + "\"");
            }
        }
        bw.write("\n</alloy>\n");
        if (!Util.close(bw))
            throw new IOException("Error writing to the file \"" + filename + "\"");
    }

    /*
     * ========================================================= ================
     * ===================
     */

    /** Does nothing if the element is malformed. */
    private static void parseView(final XMLNode x, VizState now) {
        /*
         * <view orientation=".." nodetheme=".." edgetheme=".." hidePrivate="yes/no"
         * hideMeta="yes/no" useOriginalAtomNames="yes/no" fontsize="12"> <projection>
         * .. </projection> <defaultnode../> <defaultedge../> 0 or more NODE or EDGE
         * </view>
         */
        if (!x.is("view"))
            return;
        for (XMLNode xml : x) {
            if (xml.is("projection")) {
                now.deprojectAll();
                for (AlloyType t : parseProjectionList(now, xml))
                    now.project(t);
            }
        }
        if (has(x, "useOriginalAtomNames"))
            now.useOriginalName(getbool(x, "useOriginalAtomNames"));
        if (has(x, "hidePrivate"))
            now.hidePrivate(getbool(x, "hidePrivate"));
        if (has(x, "hideMeta"))
            now.hideMeta(getbool(x, "hideMeta"));
        if (has(x, "fontsize"))
            now.setFontSize(getint(x, "fontsize"));
        if (has(x, "nodetheme"))
            now.setNodePalette(parseDotPalette(x, "nodetheme"));
        if (has(x, "edgetheme"))
            now.setEdgePalette(parseDotPalette(x, "edgetheme"));
        for (XMLNode xml : x) {
            if (xml.is("defaultnode"))
                parseNodeViz(xml, now, null);
            else if (xml.is("defaultedge"))
                parseEdgeViz(xml, now, null);
            else if (xml.is("node")) {
                for (XMLNode sub : xml.getChildren("type")) {
                    AlloyType t = parseAlloyType(now, sub);
                    if (t != null)
                        parseNodeViz(xml, now, t);
                }
                for (XMLNode sub : xml.getChildren("set")) {
                    AlloySet s = parseAlloySet(now, sub);
                    if (s != null)
                        parseNodeViz(xml, now, s);
                }
            } else if (xml.is("edge")) {
                for (XMLNode sub : xml.getChildren("relation")) {
                    AlloyRelation r = parseAlloyRelation(now, sub);
                    if (r != null)
                        parseEdgeViz(xml, now, r);
                }
            }
        }
    }

    /*
     * ========================================================= ================
     * ===================
     */

    /** Writes nothing if the argument is null. */
    private static void writeView(PrintWriter out, VizState view) throws IOException {
        if (view == null)
            return;
        VizState defaultView = new VizState(view.getOriginalInstance());
        out.write("<view");
        writeDotPalette(out, "nodetheme", view.getNodePalette(), defaultView.getNodePalette());
        writeDotPalette(out, "edgetheme", view.getEdgePalette(), defaultView.getEdgePalette());
        if (view.useOriginalName() != defaultView.useOriginalName()) {
            out.write(" useOriginalAtomNames=\"");
            out.write(view.useOriginalName() ? "yes" : "no");
            out.write("\"");
        }
        if (view.hidePrivate() != defaultView.hidePrivate()) {
            out.write(" hidePrivate=\"");
            out.write(view.hidePrivate() ? "yes" : "no");
            out.write("\"");
        }
        if (view.hideMeta() != defaultView.hideMeta()) {
            out.write(" hideMeta=\"");
            out.write(view.hideMeta() ? "yes" : "no");
            out.write("\"");
        }
        if (view.getFontSize() != defaultView.getFontSize()) {
            out.write(" fontsize=\"" + view.getFontSize() + "\"");
        }
        out.write(">\n");
        if (view.getProjectedTypes().size() > 0)
            writeProjectionList(out, view.getProjectedTypes());
        out.write("\n<defaultnode" + writeNodeViz(view, defaultView, null));
        out.write("/>\n\n<defaultedge" + writeEdgeViz(view, defaultView, null));
        out.write("/>\n");
        // === nodes ===
        Set<AlloyNodeElement> types = new TreeSet<AlloyNodeElement>();
        types.addAll(view.getOriginalModel().getTypes());
        types.addAll(view.getCurrentModel().getTypes());
        types.addAll(view.getOriginalModel().getSets());
        types.addAll(view.getCurrentModel().getSets());
        Map<String,Set<AlloyNodeElement>> viz2node = new TreeMap<String,Set<AlloyNodeElement>>();
        for (AlloyNodeElement t : types) {
            String str = writeNodeViz(view, defaultView, t);
            Set<AlloyNodeElement> nodes = viz2node.get(str);
            if (nodes == null)
                viz2node.put(str, nodes = new TreeSet<AlloyNodeElement>());
            nodes.add(t);
        }
        for (Map.Entry<String,Set<AlloyNodeElement>> e : viz2node.entrySet()) {
            out.write("\n<node" + e.getKey() + ">\n");
            for (AlloyNodeElement ts : e.getValue()) {
                if (ts instanceof AlloyType)
                    writeAlloyType(out, (AlloyType) ts);
                else if (ts instanceof AlloySet)
                    writeAlloySet(out, (AlloySet) ts);
            }
            out.write("</node>\n");
        }
        // === edges ===
        Set<AlloyRelation> rels = new TreeSet<AlloyRelation>();
        rels.addAll(view.getOriginalModel().getRelations());
        rels.addAll(view.getCurrentModel().getRelations());
        Map<String,Set<AlloyRelation>> viz2edge = new TreeMap<String,Set<AlloyRelation>>();
        for (AlloyRelation r : rels) {
            String str = writeEdgeViz(view, defaultView, r);
            if (str.length() == 0)
                continue;
            Set<AlloyRelation> edges = viz2edge.get(str);
            if (edges == null)
                viz2edge.put(str, edges = new TreeSet<AlloyRelation>());
            edges.add(r);
        }
        for (Map.Entry<String,Set<AlloyRelation>> e : viz2edge.entrySet()) {
            out.write("\n<edge" + e.getKey() + ">\n");
            for (AlloyRelation r : e.getValue())
                writeAlloyRelation(out, r);
            out.write("</edge>\n");
        }
        // === done ===
        out.write("\n</view>\n");
    }

    /*
     * ========================================================= ================
     * ===================
     */

    /** Return null if the element is malformed. */
    private static AlloyType parseAlloyType(VizState now, XMLNode x) {
        /*
         * class AlloyType implements AlloyNodeElement { String name; } <type
         * name="the type name"/>
         */
        if (!x.is("type"))
            return null;
        String name = x.getAttribute("name");
        if (name.length() == 0)
            return null;
        else
            return now.getCurrentModel().hasType(name);
    }

    /** Writes nothing if the argument is null. */
    private static void writeAlloyType(PrintWriter out, AlloyType x) throws IOException {
        if (x != null)
            Util.encodeXMLs(out, "   <type name=\"", x.getName(), "\"/>\n");
    }

    /*
     * ========================================================= ================
     * ===================
     */

    /** Return null if the element is malformed. */
    private static AlloySet parseAlloySet(VizState now, XMLNode x) {
        /*
         * class AlloySet implements AlloyNodeElement { String name; AlloyType type; }
         * <set name="name" type="name"/>
         */
        if (!x.is("set"))
            return null;
        String name = x.getAttribute("name"), type = x.getAttribute("type");
        if (name.length() == 0 || type.length() == 0)
            return null;
        AlloyType t = now.getCurrentModel().hasType(type);
        if (t == null)
            return null;
        else
            return now.getCurrentModel().hasSet(name, t);
    }

    /** Writes nothing if the argument is null. */
    private static void writeAlloySet(PrintWriter out, AlloySet x) throws IOException {
        if (x != null)
            Util.encodeXMLs(out, "   <set name=\"", x.getName(), "\" type=\"", x.getType().getName(), "\"/>\n");
    }

    /*
     * ========================================================= ================
     * ===================
     */

    /** Return null if the element is malformed. */
    private static AlloyRelation parseAlloyRelation(VizState now, XMLNode x) {
        /*
         * <relation name="name"> 2 or more <type name=".."/> </relation>
         */
        List<AlloyType> ans = new ArrayList<AlloyType>();
        if (!x.is("relation"))
            return null;
        String name = x.getAttribute("name");
        if (name.length() == 0)
            return null;
        for (XMLNode sub : x.getChildren("type")) {
            String typename = sub.getAttribute("name");
            if (typename.length() == 0)
                return null;
            AlloyType t = now.getCurrentModel().hasType(typename);
            if (t == null)
                return null;
            ans.add(t);
        }
        if (ans.size() < 2)
            return null;
        else
            return now.getCurrentModel().hasRelation(name, ans);
    }

    /** Writes nothing if the argument is null. */
    private static void writeAlloyRelation(PrintWriter out, AlloyRelation x) throws IOException {
        if (x == null)
            return;
        Util.encodeXMLs(out, "   <relation name=\"", x.getName(), "\">");
        for (AlloyType t : x.getTypes())
            Util.encodeXMLs(out, " <type name=\"", t.getName(), "\"/>");
        out.write(" </relation>\n");
    }

    /*
     * ========================================================= ================
     * ===================
     */

    /**
     * Always returns a nonnull (though possibly empty) set of AlloyType.
     */
    private static Set<AlloyType> parseProjectionList(VizState now, XMLNode x) {
        /*
         * <projection> 0 or more <type name=".."/> </projection>
         */
        Set<AlloyType> ans = new TreeSet<AlloyType>();
        if (x.is("projection"))
            for (XMLNode sub : x.getChildren("type")) {
                String name = sub.getAttribute("name");
                if (name.length() == 0)
                    continue;
                AlloyType t = now.getOriginalModel().hasType(name);
                if (t != null)
                    ans.add(t);
            }
        return ans;
    }

    /**
     * Writes an empty Projection tag if the argument is null or empty
     */
    private static void writeProjectionList(PrintWriter out, Set<AlloyType> types) throws IOException {
        if (types == null || types.size() == 0) {
            out.write("\n<projection/>\n");
            return;
        }
        out.write("\n<projection>");
        for (AlloyType t : types)
            Util.encodeXMLs(out, " <type name=\"", t.getName(), "\"/>");
        out.write(" </projection>\n");
    }

    /*
     * ========================================================= ================
     * ===================
     */

    /**
     * Do nothing if the element is malformed; note: x can be null.
     */
    private static void parseNodeViz(XMLNode xml, VizState view, AlloyNodeElement x) {
        /*
         * <node visible="inherit/yes/no" label=".." color=".." shape=".." style=".."
         * showlabel="inherit/yes/no" showinattr="inherit/yes/no"
         * hideunconnected="inherit/yes/no" nubmeratoms="inherit/yes/no"> zero or more
         * SET or TYPE </node> Each attribute, if omitted, means "no change". Note:
         * BOOLEAN is tristate.
         */
        if (has(xml, "visible"))
            view.nodeVisible.put(x, getbool(xml, "visible"));
        if (has(xml, "hideunconnected"))
            view.hideUnconnected.put(x, getbool(xml, "hideunconnected"));
        if (x == null || x instanceof AlloySet) {
            AlloySet s = (AlloySet) x;
            if (has(xml, "showlabel"))
                view.showAsLabel.put(s, getbool(xml, "showlabel"));
            if (has(xml, "showinattr"))
                view.showAsAttr.put(s, getbool(xml, "showinattr"));
        }
        if (x == null || x instanceof AlloyType) {
            AlloyType t = (AlloyType) x;
            if (has(xml, "numberatoms"))
                view.number.put(t, getbool(xml, "numberatoms"));
        }
        if (has(xml, "style"))
            view.nodeStyle.put(x, parseDotStyle(xml));
        if (has(xml, "color"))
            view.nodeColor.put(x, parseDotColor(xml));
        if (has(xml, "shape"))
            view.shape.put(x, parseDotShape(xml));
        if (has(xml, "label"))
            view.label.put(x, xml.getAttribute("label"));
    }

    /**
     * Returns the String representation of an AlloyNodeElement's settings.
     */
    private static String writeNodeViz(VizState view, VizState defaultView, AlloyNodeElement x) throws IOException {
        StringWriter sw = new StringWriter();
        PrintWriter out = new PrintWriter(sw);
        writeBool(out, "visible", view.nodeVisible.get(x), defaultView.nodeVisible.get(x));
        writeBool(out, "hideunconnected", view.hideUnconnected.get(x), defaultView.hideUnconnected.get(x));
        if (x == null || x instanceof AlloySet) {
            AlloySet s = (AlloySet) x;
            writeBool(out, "showlabel", view.showAsLabel.get(s), defaultView.showAsLabel.get(s));
            writeBool(out, "showinattr", view.showAsAttr.get(s), defaultView.showAsAttr.get(s));
        }
        if (x == null || x instanceof AlloyType) {
            AlloyType t = (AlloyType) x;
            writeBool(out, "numberatoms", view.number.get(t), defaultView.number.get(t));
        }
        writeDotStyle(out, view.nodeStyle.get(x), defaultView.nodeStyle.get(x));
        writeDotShape(out, view.shape.get(x), defaultView.shape.get(x));
        writeDotColor(out, view.nodeColor.get(x), defaultView.nodeColor.get(x));
        if (x != null && !view.label.get(x).equals(defaultView.label.get(x)))
            Util.encodeXMLs(out, " label=\"", view.label.get(x), "\"");
        if (out.checkError())
            throw new IOException("PrintWriter IO Exception!");
        return sw.toString();
    }

    /*
     * ========================================================= ================
     * ===================
     */

    /**
     * Do nothing if the element is malformed; note: x can be null.
     */
    private static void parseEdgeViz(XMLNode xml, VizState view, AlloyRelation x) {
        /*
         * <edge visible="inherit/yes/no" label=".." color=".." style=".." weight=".."
         * constraint=".." attribute="inherit/yes/no" merge="inherit/yes/no"
         * layout="inherit/yes/no"> zero or more RELATION </edge> Each attribute, if
         * omitted, means "no change". Note: BOOLEAN is tristate.
         */
        if (has(xml, "visible"))
            view.edgeVisible.put(x, getbool(xml, "visible"));
        if (has(xml, "attribute"))
            view.attribute.put(x, getbool(xml, "attribute"));
        if (has(xml, "merge"))
            view.mergeArrows.put(x, getbool(xml, "merge"));
        if (has(xml, "layout"))
            view.layoutBack.put(x, getbool(xml, "layout"));
        if (has(xml, "constraint"))
            view.constraint.put(x, getbool(xml, "constraint"));
        if (has(xml, "style"))
            view.edgeStyle.put(x, parseDotStyle(xml));
        if (has(xml, "color"))
            view.edgeColor.put(x, parseDotColor(xml));
        if (has(xml, "weight"))
            view.weight.put(x, getint(xml, "weight"));
        if (has(xml, "label"))
            view.label.put(x, xml.getAttribute("label"));
    }

    /**
     * Returns the String representation of an AlloyRelation's settings.
     */
    private static String writeEdgeViz(VizState view, VizState defaultView, AlloyRelation x) throws IOException {
        StringWriter sw = new StringWriter();
        PrintWriter out = new PrintWriter(sw);
        writeDotColor(out, view.edgeColor.get(x), defaultView.edgeColor.get(x));
        writeDotStyle(out, view.edgeStyle.get(x), defaultView.edgeStyle.get(x));
        writeBool(out, "visible", view.edgeVisible.get(x), defaultView.edgeVisible.get(x));
        writeBool(out, "merge", view.mergeArrows.get(x), defaultView.mergeArrows.get(x));
        writeBool(out, "layout", view.layoutBack.get(x), defaultView.layoutBack.get(x));
        writeBool(out, "attribute", view.attribute.get(x), defaultView.attribute.get(x));
        writeBool(out, "constraint", view.constraint.get(x), defaultView.constraint.get(x));
        if (view.weight.get(x) != defaultView.weight.get(x))
            out.write(" weight=\"" + view.weight.get(x) + "\"");
        if (x != null && !view.label.get(x).equals(defaultView.label.get(x)))
            Util.encodeXMLs(out, " label=\"", view.label.get(x), "\"");
        if (out.checkError())
            throw new IOException("PrintWriter IO Exception!");
        return sw.toString();
    }

    /*
     * ========================================================= ================
     * ===================
     */

    /**
     * Returns null if the attribute doesn't exist, or is malformed.
     */
    private static DotPalette parseDotPalette(XMLNode x, String key) {
        return DotPalette.parse(x.getAttribute(key));
    }

    /** Writes nothing if value==defaultValue. */
    private static void writeDotPalette(PrintWriter out, String key, DotPalette value, DotPalette defaultValue) throws IOException {
        if (value != defaultValue)
            Util.encodeXMLs(out, " " + key + "=\"", value == null ? "inherit" : value.toString(), "\"");
    }

    /*
     * ========================================================= ================
     * ===================
     */

    /**
     * Returns null if the attribute doesn't exist, or is malformed.
     */
    private static DotColor parseDotColor(XMLNode x) {
        return DotColor.parse(x.getAttribute("color"));
    }

    /** Writes nothing if value==defaultValue. */
    private static void writeDotColor(PrintWriter out, DotColor value, DotColor defaultValue) throws IOException {
        if (value != defaultValue)
            Util.encodeXMLs(out, " color=\"", value == null ? "inherit" : value.toString(), "\"");
    }

    /*
     * ========================================================= ================
     * ===================
     */

    /**
     * Returns null if the attribute doesn't exist, or is malformed.
     */
    private static DotShape parseDotShape(XMLNode x) {
        return DotShape.parse(x.getAttribute("shape"));
    }

    /** Writes nothing if value==defaultValue. */
    private static void writeDotShape(PrintWriter out, DotShape value, DotShape defaultValue) throws IOException {
        if (value != defaultValue)
            Util.encodeXMLs(out, " shape=\"", value == null ? "inherit" : value.toString(), "\"");
    }

    /*
     * ========================================================= ================
     * ===================
     */

    /**
     * Returns null if the attribute doesn't exist, or is malformed.
     */
    private static DotStyle parseDotStyle(XMLNode x) {
        return DotStyle.parse(x.getAttribute("style"));
    }

    /** Writes nothing if value==defaultValue. */
    private static void writeDotStyle(PrintWriter out, DotStyle value, DotStyle defaultValue) throws IOException {
        if (value != defaultValue)
            Util.encodeXMLs(out, " style=\"", value == null ? "inherit" : value.toString(), "\"");
    }

    /*
     * ========================================================= ================
     * ===================
     */

    /**
     * Returns null if the attribute doesn't exist, or is malformed.
     */
    private static Boolean getbool(XMLNode x, String attr) {
        String value = x.getAttribute(attr);
        if (value.equalsIgnoreCase("yes") || value.equalsIgnoreCase("true"))
            return Boolean.TRUE;
        if (value.equalsIgnoreCase("no") || value.equalsIgnoreCase("false"))
            return Boolean.FALSE;
        return null;
    }

    /**
     * Writes nothing if the value is equal to the default value.
     */
    private static void writeBool(PrintWriter out, String key, Boolean value, Boolean defaultValue) throws IOException {
        if (value == null && defaultValue == null)
            return;
        if (value != null && defaultValue != null && value.booleanValue() == defaultValue.booleanValue())
            return;
        out.write(' ');
        out.write(key);
        if (value == null)
            out.write("=\"inherit\"");
        else
            out.write(value ? "=\"yes\"" : "=\"no\"");
    }

    /*
     * ========================================================= ================
     * ===================
     */

    /**
     * Returns true if the XML element has the given attribute.
     */
    private static boolean has(XMLNode x, String attr) {
        return x.getAttribute(attr, null) != null;
    }

    /**
     * Returns 0 if the attribute doesn't exist, or is malformed.
     */
    private static int getint(XMLNode x, String attr) {
        String value = x.getAttribute(attr);
        int i;
        try {
            i = Integer.parseInt(value);
        } catch (NumberFormatException ex) {
            i = 0;
        }
        return i;
    }
}
