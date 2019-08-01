package edu.mit.csail.sdg.alloy4whole.instances;

import com.fasterxml.jackson.annotation.JsonProperty;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;

import java.util.ArrayList;
import java.util.List;

@XmlRootElement(name = "field")
public class Field
{
    @XmlAttribute(name = "label")
    @JsonProperty("label")
    public String label;

    @XmlAttribute(name = "ID")
    @JsonProperty("id")
    public int id;

    @XmlAttribute(name = "parentID")
    @JsonProperty("parentId")
    public int parentId;

    @XmlAttribute(name = "private")
    @JsonProperty("isPrivate")
    public String isPrivate;

    @XmlAttribute(name = "meta")
    @JsonProperty("isMeta")
    public String isMeta;

    @XmlElement(name = "tuple")
    @JsonProperty("tuples")
    public List<Tuple> tuples;

    @XmlElement(name = "types")
    @JsonProperty("types")
    public List<Types> types = new ArrayList<>();
}
