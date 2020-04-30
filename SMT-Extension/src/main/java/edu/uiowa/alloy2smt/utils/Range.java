package edu.uiowa.alloy2smt.utils;

import com.fasterxml.jackson.annotation.JsonProperty;
import com.fasterxml.jackson.databind.ObjectMapper;
import edu.mit.csail.sdg.alloy4.Pos;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlRootElement;
import java.io.ByteArrayOutputStream;
import java.io.IOException;

@XmlRootElement(name = "Range")
public class Range
{
  public Range()
  {
  }

  public Range(Pos pos)
  {
    this.filename = pos.filename;
    this.x1 = pos.x;
    this.y1 = pos.y;
    this.x2 = pos.x2;
    this.y2 = pos.y2;
  }

  @XmlAttribute(name = "filename")
  @JsonProperty("filename")
  String filename = "";

  @XmlAttribute(name = "x1")
  @JsonProperty("x1")
  int x1;

  @XmlAttribute(name = "y1")
  @JsonProperty("y1")
  int y1;

  @XmlAttribute(name = "x2")
  @JsonProperty("x2")
  int x2;

  @XmlAttribute(name = "y2")
  @JsonProperty("y2")
  int y2;

  @XmlAttribute(name = "symbolIndex")
  @JsonProperty("symbolIndex")
  int symbolIndex;

  public Pos toPos()
  {
    return new Pos(filename, x1, y1, x2, y2);
  }

  public String toJson() throws IOException
  {
    ObjectMapper objectMapper = new ObjectMapper();
    ByteArrayOutputStream outputStream = new ByteArrayOutputStream();
    objectMapper.writeValue(outputStream, this);
    return outputStream.toString();
  }

  public static Range fromJson(String json) throws IOException
  {
    ObjectMapper objectMapper = new ObjectMapper();
    Range range = objectMapper.readValue(json, Range.class);
    return range;
  }
}