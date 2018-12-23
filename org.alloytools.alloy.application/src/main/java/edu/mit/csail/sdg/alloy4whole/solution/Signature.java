package edu.mit.csail.sdg.alloy4whole.solution;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;
import java.util.List;

@XmlRootElement(name = "sig")
public class Signature
{
    @XmlElement(name = "atom")
    public List<Atom> atoms;

    @XmlAttribute(name = "label")
    public String label;

    @XmlAttribute(name = "ID")
    public int id;

    @XmlAttribute(name = "parentID")
    public int parentId;

    @XmlAttribute(name = "builtin")
    public String builtIn;
}
