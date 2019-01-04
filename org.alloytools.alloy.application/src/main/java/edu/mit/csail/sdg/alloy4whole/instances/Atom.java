package edu.mit.csail.sdg.alloy4whole.instances;

import com.fasterxml.jackson.annotation.JsonProperty;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlRootElement;

@XmlRootElement(name = "atom")
public class Atom
{
    @XmlAttribute(name = "label")
    @JsonProperty("label")
    public String label;

    public Atom()
    {
    }

    public Atom(String label)
    {
        this.label = label;
    }
}
