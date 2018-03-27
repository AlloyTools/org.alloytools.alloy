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

package edu.mit.csail.sdg.alloy4;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.Reader;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.NoSuchElementException;
import java.util.Set;

/** Immutable; this class represents an XML element node. */

public final class XMLNode implements Iterable<XMLNode> {

    /** The type of the element; never null. */
    private String                   type = "";

    /** If type is text, this is the text. */
    private String                   text = "";

    /** The set of (key,value) pairs; never null. */
    private final Map<String,String> map  = new LinkedHashMap<String,String>();

    /** The list of direct children nodes. */
    private final List<XMLNode>      sub  = new ArrayList<XMLNode>();

    /** Constructs an empty XMLNode object. */
    private XMLNode() {}

    /** Returns the number of direct subnodes. */
    public int count() {
        return sub.size();
    }

    /** Returns an unmodifiable view of the attributes. */
    public Set<Entry<String,String>> attributes() {
        return Collections.unmodifiableMap(map).entrySet();
    }

    /** Dump the content to a String. */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        toString(sb, 0);
        return sb.toString();
    }

    /** Dump the content to a StringBuilder. */
    public void toString(StringBuilder sb, int indent) {
        for (int i = 0; i < indent; i++)
            sb.append(' ');
        if (text.length() > 0) {
            Util.encodeXML(sb, text);
            sb.append('\n');
            return;
        }
        Util.encodeXMLs(sb, "<", type);
        for (Map.Entry<String,String> e : map.entrySet()) {
            Util.encodeXMLs(sb, " ", e.getKey(), "=\"", e.getValue(), "\"");
        }
        if (sub.size() == 0) {
            sb.append("/>\n");
            return;
        }
        sb.append(">\n");
        for (XMLNode x : sub)
            x.toString(sb, indent + 2);
        for (int i = 0; i < indent; i++)
            sb.append(' ');
        Util.encodeXMLs(sb, "</", type, ">\n");
    }

    /**
     * Simple parser based on XML Specification 1.0 taking into account XML
     * Specification Errata up to 2008/Jan/18.
     */
    private static final class XMLParser {

        /** True if we want to read text data also. */
        private final boolean wantText;

        /** The reader for the input XML file. */
        private final Reader  reader;

        /** The current x position in the file. */
        private int           x    = 1;

        /** The current y position in the file. */
        private int           y    = 1;

        /**
         * The current "readahead" character; -2 if the readahead cache is empty; -1 if
         * EOF is detected; otherwise it is one char.
         */
        private int           read = (-2);

        /**
         * Constructor is private, since we want only XMLNode to be able to construct an
         * instance of this class.
         */
        private XMLParser(Reader reader, boolean wantText) {
            this.wantText = wantText;
            if (reader instanceof BufferedReader)
                this.reader = reader;
            else
                this.reader = new BufferedReader(reader);
        }

        /**
         * Throws an IOException with the given msg, and associate with it the current
         * line and column location.
         */
        private void malform(String msg) throws IOException {
            throw new IOException("Error at line " + y + " column " + x + ": " + msg);
        }

        /**
         * Read the next character.
         *
         * @throws IOException if end-of-file is reached.
         * @throws IOException if an I/O error occurred.
         */
        private int read() throws IOException {
            if (read < (-1))
                read = reader.read();
            if (read < 0) {
                malform("Unexpected end of file.");
            } else if (read == '\n') {
                x = 1;
                y++;
            } else {
                x++;
            }
            int ans = read;
            read = -2;
            return ans;
        }

        /**
         * Peek without consuming the next character, or return -1 if end-of-file is
         * reached.
         *
         * @throws IOException if an I/O error occurred.
         */
        private int peek() throws IOException {
            if (read < (-1))
                read = reader.read();
            return read;
        }

        /**
         * Consume up to and including the consecutive characters "char1" and "char2".
         *
         * @throws IOException if we reached end-of-file without seeing the pattern.
         * @throws IOException if an I/O error occurred.
         */
        private void skipUntil(int char1, int char2) throws IOException {
            while (true) {
                int ch = read();
                if (ch == char1 && peek() == char2) {
                    read = (-2);
                    return;
                }
            }
        }

        /**
         * If the next N characters match the given string (where N == length of
         * string), then consume them, else throw IOException.
         *
         * @throws IOException if the next N characters do not match the given string.
         * @throws IOException if an I/O error occurred.
         */
        private void expect(String string) throws IOException {
            int saveX = x, saveY = y;
            for (int i = 0; i < string.length(); i++) {
                if (read() != string.charAt(i)) {
                    x = saveX;
                    y = saveY;
                    malform("Expects the string \"" + string + "\"");
                }
            }
        }

        /**
         * Skip whitespace if any, then return the first non-whitespace character after
         * that.
         *
         * @throws IOException if after skipping 0 or more white space character we
         *             reach end-of-file.
         * @throws IOException if an I/O error occurred.
         */
        private int skipSpace() throws IOException {
            while (true) {
                int ch = read();
                if (ch != ' ' && ch != '\t' && ch != '\r' && ch != '\n')
                    return ch;
            }
        }

        /*
         * Taking the 79 grammar rules from XML specification, and after making
         * conservative simplifications, we get these rules: ("conservative" in that
         * well-formed XML documents parse correctly, but some malformed documents also
         * parse successfully) S ::= (#x20 | #x9 | #xD | #xA)+ Name ::= (
         * [A-Za-z0-9_:.-] | [#xC0-#xEFFFF] )+ Nmtoken ::= ( [A-Za-z0-9_:.-] |
         * [#xC0-#xEFFFF] )+ Reference ::= '&' Name ';' | '&#' [0-9]+ ';' | '&#x'
         * [0-9a-fA-F]+ ';' PEReference ::= '%' Name ';' SystemLiteral ::= '...' | "..."
         * PubidLiteral ::= '...' | "..." AttValue ::= '...' | "..." EntityValue ::=
         * '...' | "..." DefaultDecl ::= ( '...' | "..." | [%()|#*?+,] | Name | S )*
         * ExternalID ::= ( '...' | "..." | [%()|#*?+,] | Name | S )* PublicID ::= (
         * '...' | "..." | [%()|#*?+,] | Name | S )* NotationType ::= ( '...' | "..." |
         * [%()|#*?+,] | Name | S )* Enumeration ::= ( '...' | "..." | [%()|#*?+,] |
         * Name | S )* EnumeratedType ::= ( '...' | "..." | [%()|#*?+,] | Name | S )*
         * AttType ::= ( '...' | "..." | [%()|#*?+,] | Name | S )* Mixed ::= ( '...' |
         * "..." | [%()|#*?+,] | Name | S )* children ::= ( '...' | "..." | [%()|#*?+,]
         * | Name | S )* contentspec ::= ( '...' | "..." | [%()|#*?+,] | Name | S )*
         * PEDef ::= ( '...' | "..." | [%()|#*?+,] | Name | S )* NDataDecl ::= ( '...' |
         * "..." | [%()|#*?+,] | Name | S )* EntityDef ::= ( '...' | "..." | [%()|#*?+,]
         * | Name | S )* NotationDecl ::= '<!NOTATION' ( '...' | "..." | [%()|#*?+,] |
         * Name | S )* '>' AttlistDecl ::= '<!ATTLIST' ( '...' | "..." | [%()|#*?+,] |
         * Name | S )* '>' elementdecl ::= '<!ELEMENT' ( '...' | "..." | [%()|#*?+,] |
         * Name | S )* '>' EntityDecl ::= '<!ENTITY' ( '...' | "..." | [%()|#*?+,] |
         * Name | S )* '>' PI ::= '<?' ... '?>' Comment ::= '<!--' ([^-] | ('-' [^-])))*
         * '-->' Misc ::= Comment | PI | S doctypedecl ::= '<!DOCTYPE' S Name (S
         * ExternalID)? S? ('[' intSubset ']' S?)? '>' intSubset ::= (elementdecl |
         * AttlistDecl | EntityDecl | NotationDecl | PI | Comment | PEReference | S)*
         * SkipNondata(false) will skip zero or more instance of the below, and thus it
         * will consume (Misc | doctypedecl)* SPACE TAB CR LF <?...?> <!--...--> '<!'
         * followed by SkipNondata(true) followed by '>' SkipNondata(true) will skip
         * zero or more instances of the below, and thus it will consume intSubset*
         * SPACE TAB CR LF <?...?> <!--...--> '<!' followed by SkipNondata(true)
         * followed by '>' '[' followed by SkipNondata(true) followed by ']' '...' "..."
         * any char that is not '<' nor '>' nor '[' nor ']' nor ''' nor '"'
         */

        /**
         * Skip as much nondata as possible, then return the first character after that
         * (or -1 if we end up at end-of-file).
         * <p>
         * Specifically, skipNondata(false) consumes (Misc | doctypedecl)* from XML
         * specification
         * <p>
         * Likewise, skipNondata(true) consumes (intSubset)* from XML specification
         *
         * @throws IOException if the XML input is malformed.
         * @throws IOException if an I/O error occurred.
         */
        private int skipNondata(boolean inner) throws IOException {
            while (true) {
                int ch = peek();
                if (ch < 0)
                    return -1;
                read = -2;
                if (ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n')
                    continue;
                if (ch == '<') {
                    ch = read();
                    if (ch == '?') {
                        skipUntil('?', '>');
                        continue;
                    }
                    if (ch != '!') {
                        read = ch;
                        return '<';
                    }
                    if (peek() == '-') {
                        read = -2;
                        if (read() != '-')
                            malform("Expects start of <!--...-->");
                        skipUntil('-', '-');
                        if (read() != '>')
                            malform("Expects end of <!--...-->");
                        continue;
                    }
                    if (skipNondata(true) != '>')
                        malform("Expects end of <!...>");
                } else if (!inner || ch == ']' || ch == '>') {
                    return ch;
                } else if (ch == '[') {
                    if (skipNondata(true) != ']')
                        malform("Expects end of [...]");
                } else if (ch == '\'' || ch == '\"') {
                    while (read() != ch) {}
                }
            }
        }

        /**
         * Parse an element name or attribute name.
         *
         * @throws IOException if the XML input is malformed.
         * @throws IOException if an I/O error occurred.
         */
        private String parseName() throws IOException {
            StringBuilder sb = new StringBuilder();
            while (true) {
                int ch = read();
                if (ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n' || ch == '=' || ch == '/' || ch == '<' || ch == '>' || ch == '[' || ch == ']') {
                    read = ch;
                    return sb.toString();
                }
                sb.append((char) ch);
            }
        }

        /**
         * Parse a value up to delim (which is always either ' or "), assuming the
         * initial ' or " has already been consumed.
         *
         * @throws IOException if the XML input is malformed.
         * @throws IOException if an I/O error occurred.
         */
        private String parseValue(int delim) throws IOException {
            StringBuilder sb = new StringBuilder(), sb2 = null;
            while (true) {
                int ch = read();
                if (ch == delim)
                    return sb.toString();
                if (ch == '&') {
                    if (sb2 == null)
                        sb2 = new StringBuilder();
                    else
                        sb2.setLength(0);
                    while ((ch = read()) != ';')
                        sb2.append((char) ch);
                    if (sb2.length() > 2 && sb2.charAt(0) == '#' && sb2.charAt(1) == 'x') {
                        try {
                            ch = Integer.parseInt(sb2.substring(2), 16);
                        } catch (NumberFormatException ex) {
                            ch = (-1);
                        }
                    } else if (sb2.length() > 1 && sb2.charAt(0) == '#') {
                        try {
                            ch = Integer.parseInt(sb2.substring(1));
                        } catch (NumberFormatException ex) {
                            ch = (-1);
                        }
                    } else {
                        String name = sb2.toString();
                        if (name.equals("amp"))
                            ch = '&';
                        else if (name.equals("quot"))
                            ch = '"';
                        else if (name.equals("apos"))
                            ch = '\'';
                        else if (name.equals("lt"))
                            ch = '<';
                        else if (name.equals("gt"))
                            ch = '>';
                        else
                            ch = (-1);
                    }
                    if (ch < 0)
                        malform("The entity \"&" + sb2.toString() + ";\" is unknown.");
                }
                sb.append((char) ch);
            }
        }

        /*
         * Below are the grammar rules for "element":
         * ========================================== element ::= '<' Name (S Name S?
         * '=' S? AttValue)* S? '/>' | '<' Name (S Name S? '=' S? AttValue)* S? '>'
         * content '</' Name S? '>' content ::= CharData? ((element | Reference | CDSect
         * | PI | Comment) CharData?)* CDSect ::= '<![CDATA[' (Char* - (Char* ']]>'
         * Char*)) ']]>' CharData ::= [^<&]* - ([^<&]* ']]>' [^<&]*)
         */

        /**
         * Parse an element (and all its subelements), assuming the initial "less than"
         * sign has already been consumed.
         *
         * @throws IOException if the XML input is malformed.
         * @throws IOException if an I/O error occurred.
         */
        private void parseElement(XMLNode target) throws IOException {
            target.type = parseName();
            while (true) {
                boolean space = false;
                int ch = read();
                if (ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n') {
                    space = true;
                    ch = skipSpace();
                }
                if (ch == '=')
                    malform("Unexpected '='");
                if (ch == '/') {
                    if (read() != '>')
                        malform("Expects '/>'");
                    break;
                }
                if (ch == '>') {
                    parseContent(target);
                    if (!target.type.equals(parseName()))
                        malform("Start tag and end tag must have matching types.");
                    if (skipSpace() != '>')
                        malform("Expects '</" + target.type + ">'");
                    break;
                }
                if (!space)
                    malform("Whitespace needed before a (key,value) pair.");
                read = ch;
                String key = parseName();
                if (key.length() == 0)
                    malform("Attribute name cannot be empty.");
                if (skipSpace() != '=')
                    malform("Expects = after the attribute name.");
                ch = skipSpace();
                if (ch != '\'' && ch != '\"')
                    malform("Expects \' or \" as the start of the attribute value.");
                String value = parseValue(ch);
                target.map.put(key, value);
            }
        }

        /**
         * Parses the content until the rightful closing "LESS THAN SIGN followed by
         * FORWARD SLASH" are both consumed.
         *
         * @throws IOException if the XML input is malformed.
         * @throws IOException if an I/O error occurred.
         */
        private void parseContent(XMLNode parent) throws IOException {
            StringBuilder sb = wantText ? new StringBuilder() : null;
            again: while (true) {
                if (sb == null) {
                    while (read() != '<') {}
                } else {
                    sb.append(parseValue('<').replace('\r', ' ').replace('\n', ' '));
                    parent.addText(sb);
                }
                int ch = read();
                if (ch == '/')
                    return;
                if (ch == '?') {
                    skipUntil('?', '>');
                    continue;
                }
                if (ch == '!') {
                    ch = read();
                    if (ch == '-') {
                        if (read() != '-')
                            malform("Expects start of <!--...-->");
                        skipUntil('-', '-');
                        if (read() != '>')
                            malform("Expects end of <!--...-->");
                        continue;
                    }
                    if (ch != '[')
                        malform("Expects <![CDATA[...]]>");
                    expect("CDATA[");
                    for (int ah = 0, bh = 0;;) {
                        ch = read();
                        if (ah == ']' && bh == ']' && ch == '>') {
                            parent.addText(sb);
                            continue again;
                        } else {
                            if (ah > 0 && sb != null)
                                sb.append((char) ah);
                            ah = bh;
                            bh = ch;
                        }
                    }
                }
                read = ch;
                XMLNode newElem = new XMLNode();
                parseElement(newElem);
                parent.sub.add(newElem);
            }
        }
    }

    /**
     * Add a text node by removing all contents from the given StringBuilder and
     * clearing that StringBuilder.
     */
    private void addText(StringBuilder stringBuilder) {
        if (stringBuilder == null || stringBuilder.length() == 0)
            return;
        XMLNode x = new XMLNode();
        x.text = stringBuilder.toString();
        stringBuilder.setLength(0);
        sub.add(x);
    }

    /**
     * Constructs the root XMLNode by parsing an entire XML document, then close the
     * reader afterwards.
     */
    public XMLNode(Reader reader, boolean parseText) throws IOException {
        try {
            // document ::= Misc* doctypedecl? Misc* element Misc*
            XMLParser parser = new XMLParser(reader, parseText);
            if (parser.skipNondata(false) != '<')
                parser.malform("Expects start of root element.");
            parser.parseElement(this);
            if (parser.skipNondata(false) != (-1))
                parser.malform("Expects end of file.");
        } finally {
            Util.close(reader);
        }
    }

    /**
     * Constructs the root XMLNode by parsing an entire XML document, then close the
     * reader afterwards.
     */
    public XMLNode(Reader reader) throws IOException {
        try {
            // document ::= Misc* doctypedecl? Misc* element Misc*
            XMLParser parser = new XMLParser(reader, false);
            if (parser.skipNondata(false) != '<')
                parser.malform("Expects start of root element.");
            parser.parseElement(this);
            if (parser.skipNondata(false) != (-1))
                parser.malform("Expects end of file.");
        } finally {
            Util.close(reader);
        }
    }

    /**
     * Constructs the root XMLNode by parsing an entire XML document.
     */
    public XMLNode(File file) throws IOException {
        FileInputStream fis = null;
        InputStreamReader reader = null;
        try {
            // document ::= Misc* doctypedecl? Misc* element Misc*
            fis = new FileInputStream(file);
            reader = new InputStreamReader(fis, "UTF-8");
            XMLParser parser = new XMLParser(reader, false);
            if (parser.skipNondata(false) != '<')
                parser.malform("Expects start of root element.");
            parser.parseElement(this);
            if (parser.skipNondata(false) != (-1))
                parser.malform("Expects end of file.");
        } finally {
            Util.close(reader);
            Util.close(fis);
        }
    }

    /** Returns the type of the element. */
    public String getType() {
        return type;
    }

    /**
     * Returns the text if this is a text node, returns "" otherwise.
     */
    public String getText() {
        return text;
    }

    /**
     * Returns true if the type of this element is equal to the given type.
     */
    public boolean is(String type) {
        return this.type.equals(type);
    }

    /**
     * Returns a read-only iterator over the immediate subelements.
     */
    @Override
    public Iterator<XMLNode> iterator() {
        return Collections.unmodifiableList(sub).iterator();
    }

    /**
     * Returns a read-only iteration of the immediate subelements whose type is
     * equal to the given type.
     */
    public Iterable<XMLNode> getChildren(final String type) {
        return new Iterable<XMLNode>() {

            @Override
            public Iterator<XMLNode> iterator() {
                return new Iterator<XMLNode>() {

                    private final Iterator<XMLNode> it   = sub.iterator();
                    private XMLNode                 peek = null;

                    @Override
                    public boolean hasNext() {
                        while (true) {
                            if (peek != null && peek.type.equals(type))
                                return true;
                            if (!it.hasNext())
                                return false;
                            else
                                peek = it.next();
                        }
                    }

                    @Override
                    public XMLNode next() {
                        if (!hasNext())
                            throw new NoSuchElementException();
                        XMLNode ans = peek;
                        peek = null;
                        return ans;
                    }

                    @Override
                    public void remove() {
                        throw new UnsupportedOperationException();
                    }
                };
            }
        };
    }

    /**
     * Returns the value associated with the given attribute name; if the attribute
     * doesn't exist, return "".
     */
    public String getAttribute(String name) {
        String ans = map.get(name);
        return (ans == null) ? "" : ans;
    }

    /**
     * Returns the value associated with the given attribute name; if the attribute
     * doesn't exist, return the defaultValue.
     */
    public String getAttribute(String name, String defaultValue) {
        String ans = map.get(name);
        return (ans == null) ? defaultValue : ans;
    }
}
