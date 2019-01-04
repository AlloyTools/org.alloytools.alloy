package edu.mit.csail.sdg.alloy4whole.instances;

import com.fasterxml.jackson.annotation.JsonProperty;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;
import java.util.List;

@XmlRootElement(name = "instance")
public class Instance
{
    @XmlElement(name = "sig")
    @JsonProperty("signatures")
    public List<Signature> signatures;

    @XmlElement(name = "field")
    @JsonProperty("fields")
    public List<Field> fields;

    @XmlAttribute(name = "bitwidth")
    @JsonProperty("bitWidth")
    public int bitWidth = 4;

    @XmlAttribute(name = "maxseq")
    @JsonProperty("maxSeq")
    public int maxSeq = 4;

    @XmlAttribute(name = "command")
    @JsonProperty("command")
    public String command;

    @XmlAttribute(name = "filename")
    @JsonProperty("fileName")
    public String fileName;
}
