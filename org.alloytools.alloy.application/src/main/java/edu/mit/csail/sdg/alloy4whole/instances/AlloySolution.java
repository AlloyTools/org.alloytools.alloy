package edu.mit.csail.sdg.alloy4whole.instances;

import com.fasterxml.jackson.annotation.JsonProperty;
import com.fasterxml.jackson.databind.ObjectMapper;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Marshaller;
import javax.xml.bind.Unmarshaller;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;

@XmlRootElement(name = "alloy")
public class AlloySolution
{
    @XmlElement(name = "instance")
    @JsonProperty("instances")
    public List<Instance> instances;

    @XmlAttribute(name = "builddate")
    @JsonProperty("buildDate")
    public String buildDate;

    @XmlElement(name = "source")
    @JsonProperty("alloyFiles")
    public List<AlloyFile> alloyFiles;

    public Map<String, String> getAlloyFiles()
    {
        Map<String, String> files = new HashMap<>();
        if(alloyFiles != null)
        {
            for (AlloyFile file: alloyFiles)
            {
                files.put(file.fileName, file.content);
            }
        }
        return files;
    }

    public void writeToXml(String xmlFile) throws JAXBException
    {
        JAXBContext context = JAXBContext.newInstance(AlloySolution.class);
        Marshaller marshaller = context.createMarshaller();
        marshaller.setProperty(Marshaller.JAXB_FORMATTED_OUTPUT, Boolean.TRUE);
        marshaller.marshal(this, new File(xmlFile));
    }

    public static AlloySolution readFromXml(String xmlFile) throws JAXBException
    {
        JAXBContext context = JAXBContext.newInstance(AlloySolution.class);
        Unmarshaller unmarshaller = context.createUnmarshaller();
        AlloySolution alloySolution = (AlloySolution) unmarshaller.unmarshal(new File(xmlFile));
        return alloySolution;
    }

    public void writeToJson(String jsonFile) throws IOException
    {
        ObjectMapper objectMapper = new ObjectMapper();
        objectMapper.writerWithDefaultPrettyPrinter().writeValue(new File(jsonFile), this);
    }

    public static AlloySolution readFromJson(String jsonFile) throws IOException
    {
        ObjectMapper objectMapper = new ObjectMapper();
        AlloySolution alloySolution = objectMapper.readValue(new File(jsonFile), AlloySolution.class);
        return alloySolution;
    }
}
