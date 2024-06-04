/*
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 * Pardinus -- Copyright (c) 2013-present, Nuno Macedo, INESC TEC
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */
package org.alloytools.solvers.natv.electrod;

import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

import kodkod.ast.Relation;
import kodkod.engine.unbounded.InvalidUnboundedSolution;
import kodkod.instance.Instance;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TemporalInstance;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;
import kodkod.util.ints.IndexedEntry;

/**
 * Processes the output of an Electrod solving process into a
 * {@link TemporalInstance temporal instance} that can be processed by
 * Kodkod/Pardinus. Some renaming has been done between on the atoms/relations
 * in the translation to Electrod, which must be reverted.
 *
 * @author Nuno Macedo // [HASLab] unbounded temporal model finding
 */
public class ElectrodReader {

    private List<Instance> insts;
    private int            loop;
    public int             nbvars, ctime, atime;
    private PardinusBounds bounds;
    private final Map<Relation,String> rel2name;

    /**
     * Initializes the Electrod solution reader with the original problem bounds.
     *
     * @param bounds the original bounds of the solved problem.
     */
    public ElectrodReader(PardinusBounds bounds, Map<Relation,String> rel2name) {
        this.insts = new ArrayList<Instance>();
        this.loop = -1;
        this.bounds = bounds;
        this.rel2name = rel2name;
    }

    /**
     * Reads an Electrod solution from an XML file, creating a temporal instance
     * that can be processed by Kodkod/Pardinus. Returns null if the problem is
     * unsatisfiable.
     *
     * @param string the XML Electrod solution to be parsed.
     * @return the parsed temporal instance or null if unsat.
     * @throws InvalidUnboundedSolution if the parsing fails.
     */
    public TemporalInstance read(String string) throws InvalidUnboundedSolution {
        return read(new StringReader(string));
    }

    public TemporalInstance read(Reader reader) throws InvalidUnboundedSolution {
        return read(new InputSource(reader));
    }

    public TemporalInstance read(InputSource source) throws InvalidUnboundedSolution {
        DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
        factory.setValidating(false);
        factory.setIgnoringElementContentWhitespace(true);
        try {
            DocumentBuilder builder = factory.newDocumentBuilder();
            Document doc = builder.parse(source);
            Element root = doc.getDocumentElement();
            nbvars = Integer.valueOf(root.getAttributes().getNamedItem("nbvars").getNodeValue());
            ctime = getMillis(root.getAttributes().getNamedItem("conversion-time").getNodeValue());
            atime = getMillis(root.getAttributes().getNamedItem("analysis-time").getNodeValue());
            NodeList elems = root.getChildNodes();
            int c = 0;
            for (int i = 0; i < elems.getLength(); i++) {
                if (elems.item(i).getNodeName().equals("st")) {
                    if (elems.item(i).getAttributes().getNamedItem("loop-target").getNodeValue().equals("true"))
                        loop = c;
                    insts.add(state(elems.item(i)));
                    c++;
                }
            }
        } catch (ParserConfigurationException | SAXException | IOException e) {
            throw new InvalidUnboundedSolution("Failed to parse Electrod XML.", e);
        }
        if (insts.size() == 0)
            return null;

        return new TemporalInstance(insts, loop, 1);
    }

    final static Pattern DURATION_P = Pattern.compile("(?<val>\\d+(\\.\\d+)?)(?<unit>.*)?");

    private int getMillis(String nodeValue) {
        try {
            return Integer.valueOf(nodeValue);
        } catch (NumberFormatException e) {
            Matcher m = DURATION_P.matcher(nodeValue);
            if (m.matches()) {
                double val = Double.valueOf(m.group("val"));
                String unit = m.group("unit");
                if (unit == null)
                    return (int) val;
                switch (unit) {
                    default :
                    case "ms" :
                        return (int) val;
                    case "s" :
                        return (int) (val * 1000);
                    case "m" :
                        return (int) (val * 60_000);
                }
            } else {
                return Integer.MAX_VALUE;
            }
        }
    }

    /**
     * Parses a single state of the trace as a static regular Kodkod {@link Instance
     * instance}. Atoms and relations may have been renamed by
     * {@link ElectrodPrinter#normRel(String)}, which must be reverted.
     *
     * @param node the XML node containing the state.
     * @return the static instance corresponding to the state.
     */
    private Instance state(Node node) {
        Instance inst = new Instance(bounds.universe());

        for (Relation r : bounds.relations()) {

            NodeList e = null;
            for (int i = 0; i < node.getChildNodes().getLength(); i++) {
                if (node.getChildNodes().item(i).getNodeName().equals("rel")) {
                    String nm = rel2name.get(r);
                    if (node.getChildNodes().item(i).getAttributes().getNamedItem("name").getNodeValue().equals(nm))
                        e = node.getChildNodes().item(i).getChildNodes();
                }
            }
            List<List<String>> buff__ = new ArrayList<List<String>>();

            if (e != null)
                for (int i = 0; i < e.getLength(); i++) {
                    if (e.item(i).getNodeName().equals("t")) {
                        List<String> buff_ = new ArrayList<String>();
                        for (int j = 0; j < e.item(i).getChildNodes().getLength(); j++) {
                            if (e.item(i).getChildNodes().item(j).getNodeName().equals("a")) {
                                buff_.add(e.item(i).getChildNodes().item(j).getTextContent());
                            }
                        }
                        buff__.add(buff_);
                    }
                }

            List<Tuple> buff = new ArrayList<Tuple>();
            for (List<String> buff_ : buff__) {
                List<Object> _buff = new ArrayList<Object>();
                for (String x : buff_)
                    for (int i = 0; i < bounds.universe().size(); i++) {
                        if (ElectrodPrinter.normRel(bounds.universe().atom(i).toString()).equals(x))
                            _buff.add(bounds.universe().atom(i));
                    }
                buff.add(bounds.universe().factory().tuple(_buff));
            }

            TupleSet t;
            if (buff.isEmpty())
                t = bounds.universe().factory().noneOf(r.arity());
            else
                t = bounds.universe().factory().setOf(buff);

            inst.add(r, t);
        }

        // propagate integers
        for (IndexedEntry<TupleSet> x : bounds.intBounds()) {
            inst.add(x.index(), x.value());
        }

        return inst;
    }

}
