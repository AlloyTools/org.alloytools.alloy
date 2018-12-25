package edu.mit.csail.sdg.alloy4whole.solution;

import com.fasterxml.jackson.annotation.JsonProperty;
import edu.uiowa.alloy2smt.mapping.MappingType;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;
import java.util.ArrayList;
import java.util.List;

@XmlRootElement(name = "field")
public class Field
{
    @XmlAttribute(name = "label")
    public String label;

    @XmlAttribute(name = "functionName")
    public String functionName; // function name in SMT model

    @XmlAttribute(name = "ID")
    @JsonProperty("id")
    public int id;

    @XmlAttribute(name = "parentID")
    @JsonProperty("parentId")
    public int parentId;

    @XmlAttribute(name = "private")
    public String isPrivate;

    @XmlAttribute(name = "meta")
    public String isMeta;

    @XmlElement(name = "tuple")
    @JsonProperty("tuples")
    public List<Tuple> tuples;

    @XmlElement(name = "types")
    public Types types;
}
