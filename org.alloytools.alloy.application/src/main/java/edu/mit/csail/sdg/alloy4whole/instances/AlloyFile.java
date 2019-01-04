package edu.mit.csail.sdg.alloy4whole.instances;

import com.fasterxml.jackson.annotation.JsonProperty;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlRootElement;

@XmlRootElement(name = "source")
public class AlloyFile
{
    @XmlAttribute(name = "filename")
    @JsonProperty("fileName")
    public String fileName;

    @XmlAttribute(name = "content")
    @JsonProperty("content")
    public String content;

    public AlloyFile()
    {
    }

    public AlloyFile(String fileName, String content)
    {
        this.fileName = fileName;
        this.content  = content;
    }
}
