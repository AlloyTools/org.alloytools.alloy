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

//ToDo: refactor this class with alloy Signature class
@XmlRootElement(name = "Signature")
public class MappingSignature
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

  @XmlAttribute(name = "parents")
  @JsonProperty("parents")
  public List<Integer> parents = new ArrayList<>();

  @XmlAttribute(name = "builtIn")
  @JsonProperty("builtIn")
  public boolean builtIn;

  @XmlAttribute(name = "isAbstract")
  @JsonProperty("isAbstract")
  public boolean isAbstract;

  @XmlAttribute(name = "isOne")
  @JsonProperty("isOne")
  public boolean isOne;

  @XmlAttribute(name = "isLone")
  @JsonProperty("isLone")
  public boolean isLone;

  @XmlAttribute(name = "isSome")
  @JsonProperty("isSome")
  public boolean isSome;

  @XmlAttribute(name = "isPrivate")
  @JsonProperty("isPrivate")
  public boolean isPrivate;

  @XmlAttribute(name = "isMeta")
  @JsonProperty("isMeta")
  public boolean isMeta;

  @XmlAttribute(name = "isExact")
  @JsonProperty("isExact")
  public boolean isExact;

  @XmlAttribute(name = "isEnum")
  @JsonProperty("isEnum")
  public boolean isEnum;

  @XmlAttribute(name = "isSubset")
  @JsonProperty("isSubset")
  public boolean isSubset;
}
