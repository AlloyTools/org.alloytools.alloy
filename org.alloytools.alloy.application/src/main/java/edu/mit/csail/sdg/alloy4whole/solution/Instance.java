package edu.mit.csail.sdg.alloy4whole.solution;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;
import java.util.List;

@XmlRootElement(name = "instance")
public class Instance
{
    @XmlElement(name = "sig")
    public List<Signature> signatures;

    @XmlAttribute(name = "bitwidth")
    public int bitWidth = 4;

    @XmlAttribute(name = "maxseq")
    public int maxSeq = 4;

    @XmlAttribute(name = "command")
    public String command;

    @XmlAttribute(name = "filename")
    public String fileName;
}
