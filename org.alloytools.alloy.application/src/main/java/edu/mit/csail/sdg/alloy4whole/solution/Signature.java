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
    public String builtIn; // yes/no

    @XmlAttribute(name = "abstract")
    public String isAbstract; // yes/no

    @XmlAttribute(name = "one")
    public String isOne; // yes/no

    @XmlAttribute(name = "lone")
    public String isLone; // yes/no

    @XmlAttribute(name = "some")
    public String isSome; // yes/no

    @XmlAttribute(name = "private")
    public String isPrivate; // yes/no

    @XmlAttribute(name = "meta")
    public String isMeta; // yes/no

    @XmlAttribute(name = "exact")
    public String isExact; // yes/no

    @XmlAttribute(name = "enum")
    public String isEnum; // yes/no
}
