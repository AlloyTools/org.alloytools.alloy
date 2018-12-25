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
    public String label;

    @XmlAttribute(name = "functionName")
    public String functionName; // function name in SMT model

    @XmlAttribute(name = "id")
    public int id;

    @XmlAttribute(name = "parentId")
    public int parentId;

    @XmlAttribute(name = "isPrivate")
    public boolean isPrivate;

    @XmlAttribute(name = "isMeta")
    public boolean isMeta;

    @XmlAttribute(name = "types")
    @JsonProperty("types")
    public List<MappingType> types = new ArrayList<>();

}
