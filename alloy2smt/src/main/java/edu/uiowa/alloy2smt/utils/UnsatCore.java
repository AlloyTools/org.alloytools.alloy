package edu.uiowa.alloy2smt.utils;

import com.fasterxml.jackson.annotation.JsonProperty;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlRootElement;
import java.util.ArrayList;
import java.util.List;

@XmlRootElement(name = "UnsatCore")
public class UnsatCore
{
    @XmlAttribute(name = "ranges")
    @JsonProperty("ranges")
    public List<Range> ranges = new ArrayList<>();
}
