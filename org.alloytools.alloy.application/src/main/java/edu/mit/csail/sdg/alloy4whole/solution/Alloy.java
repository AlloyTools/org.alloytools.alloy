package edu.mit.csail.sdg.alloy4whole.solution;

import java.util.List;

import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;

@XmlRootElement(name = "alloy")
public class Alloy
{
    @XmlElement(name = "instance")
    public List<Instance> instances;
}
