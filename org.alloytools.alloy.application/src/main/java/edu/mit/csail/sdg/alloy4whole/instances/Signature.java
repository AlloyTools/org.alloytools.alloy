package edu.mit.csail.sdg.alloy4whole.instances;

import com.fasterxml.jackson.annotation.JsonProperty;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;
import java.util.ArrayList;
import java.util.List;

@XmlRootElement(name = "sig")
public class Signature
{
    @XmlElement(name = "atom")
    @JsonProperty("atoms")
    public List<Atom> atoms;

    @XmlElement(name = "type")
    @JsonProperty("types")
    public List<Type> types = new ArrayList<>();

    @XmlAttribute(name = "label")
    @JsonProperty("label")
    public String label;

    @XmlAttribute(name = "ID")
    @JsonProperty("id")
    public int id;

    @XmlAttribute(name = "parentID")
    @JsonProperty("parents")
    public int parentId;

    @XmlAttribute(name = "builtin")
    @JsonProperty("builtIn")
    public String builtIn; // yes/no

    @XmlAttribute(name = "abstract")
    public String isAbstract; // yes/no

    @XmlAttribute(name = "one")
    @JsonProperty("isOne")
    public String isOne; // yes/no

    @XmlAttribute(name = "lone")
    @JsonProperty("isLone")
    public String isLone; // yes/no

    @XmlAttribute(name = "some")
    @JsonProperty("isSome")
    public String isSome; // yes/no

    @XmlAttribute(name = "private")
    public String isPrivate; // yes/no

    @XmlAttribute(name = "meta")
    @JsonProperty("isMeta")
    public String isMeta; // yes/no

    @XmlAttribute(name = "exact")
    @JsonProperty("isExact")
    public String isExact; // yes/no

    @XmlAttribute(name = "enum")
    @JsonProperty("isEnum")
    public String isEnum; // yes/no

    @Override
    public String toString()
    {
        return label;
    }
}
