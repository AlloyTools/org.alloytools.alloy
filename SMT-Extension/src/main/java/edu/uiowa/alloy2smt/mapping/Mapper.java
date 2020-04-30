/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.mapping;

import com.fasterxml.jackson.annotation.JsonProperty;
import com.fasterxml.jackson.databind.ObjectMapper;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Marshaller;
import javax.xml.bind.Unmarshaller;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlRootElement;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

@XmlRootElement(name = "Mapper")
public class Mapper
{
  @XmlAttribute(name = "Signature")
  @JsonProperty("signatures")
  public List<MappingSignature> signatures = new ArrayList<>();

  @XmlAttribute(name = "Field")
  @JsonProperty("fields")
  public List<MappingField> fields = new ArrayList<>();

  public void writeToXml(String xmlFile) throws JAXBException
  {
    JAXBContext context = JAXBContext.newInstance(Mapper.class);
    Marshaller marshaller = context.createMarshaller();
    marshaller.setProperty(Marshaller.JAXB_FORMATTED_OUTPUT, Boolean.TRUE);
    marshaller.marshal(this, new File(xmlFile));
  }

  public static Mapper readFromXml(String xmlFile) throws JAXBException
  {
    JAXBContext context = JAXBContext.newInstance(Mapper.class);
    Unmarshaller unmarshaller = context.createUnmarshaller();
    Mapper mapper = (Mapper) unmarshaller.unmarshal(new File(xmlFile));
    return mapper;
  }

  public void writeToJson(String jsonFile) throws IOException
  {
    ObjectMapper objectMapper = new ObjectMapper();
    objectMapper.writerWithDefaultPrettyPrinter().writeValue(new File(jsonFile), this);
  }

  public static Mapper readFromJson(String jsonFile) throws IOException
  {
    ObjectMapper objectMapper = new ObjectMapper();
    Mapper mapper = objectMapper.readValue(new File(jsonFile), Mapper.class);
    return mapper;
  }
}
