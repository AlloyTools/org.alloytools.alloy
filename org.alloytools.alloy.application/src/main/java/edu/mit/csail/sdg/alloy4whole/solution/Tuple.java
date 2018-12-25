package edu.mit.csail.sdg.alloy4whole.solution;

import com.fasterxml.jackson.annotation.JsonProperty;

import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;
import java.util.List;

@XmlRootElement(name = "tuple")
public class Tuple
{
    @XmlElement(name = "atom")
    @JsonProperty("atoms")
    public List<Atom> atoms;
}
