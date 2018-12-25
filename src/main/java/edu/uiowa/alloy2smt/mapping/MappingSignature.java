/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.mapping;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlRootElement;


@XmlRootElement(name = "Signature")
public class MappingSignature
{
    @XmlAttribute(name = "label")
    public String label;

    @XmlAttribute(name = "functionName")
    public String functionName; // function name in SMT model

    @XmlAttribute(name = "id")
    public int id;

    @XmlAttribute(name = "parentId")
    public int parentId;

    @XmlAttribute(name = "builtIn")
    public boolean builtIn;

    @XmlAttribute(name = "isAbstract")
    public boolean isAbstract;

    @XmlAttribute(name = "isOne")
    public boolean isOne;

    @XmlAttribute(name = "isLone")
    public boolean isLone;

    @XmlAttribute(name = "isSome")
    public boolean isSome;

    @XmlAttribute(name = "isPrivate")
    public boolean isPrivate;

    @XmlAttribute(name = "isMeta")
    public boolean isMeta;

    @XmlAttribute(name = "isExact")
    public boolean isExact;

    @XmlAttribute(name = "isEnum")
    public boolean isEnum;
}
