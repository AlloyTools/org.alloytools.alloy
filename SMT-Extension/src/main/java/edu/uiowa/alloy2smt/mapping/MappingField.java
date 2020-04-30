/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.mapping;

import com.fasterxml.jackson.annotation.JsonProperty;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlRootElement;
import java.util.ArrayList;
import java.util.List;

@XmlRootElement(name = "Field")
public class MappingField
{
  @XmlAttribute(name = "label")
  @JsonProperty("label")
  public String label;

  @XmlAttribute(name = "functionName")
  @JsonProperty("functionName")
  public String functionName; // function name in SMT model

  @XmlAttribute(name = "id")
  @JsonProperty("id")
  public int id;

  @XmlAttribute(name = "parentId")
  @JsonProperty("parentId")
  public int parentId;

  @XmlAttribute(name = "isPrivate")
  @JsonProperty("isPrivate")
  public boolean isPrivate;

  @XmlAttribute(name = "isMeta")
  @JsonProperty("isMeta")
  public boolean isMeta;

  @XmlAttribute(name = "types")
  @JsonProperty("types")
  public List<List<MappingType>> types = new ArrayList<>();
}
