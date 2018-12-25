package edu.mit.csail.sdg.alloy4whole.solution;

import com.fasterxml.jackson.annotation.JsonProperty;

import java.io.File;
import java.util.List;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Marshaller;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;

@XmlRootElement(name = "alloy")
public class Alloy
{
    @XmlElement(name = "instance")
    @JsonProperty("instances")
    public List<Instance> instances;

    public void writeToXml(String xmlFile) throws JAXBException
    {
        JAXBContext context = JAXBContext.newInstance(Alloy.class);
        Marshaller m = context.createMarshaller();
        m.setProperty(Marshaller.JAXB_FORMATTED_OUTPUT, Boolean.TRUE);
        m.marshal(this, new File(xmlFile));
    }
}
