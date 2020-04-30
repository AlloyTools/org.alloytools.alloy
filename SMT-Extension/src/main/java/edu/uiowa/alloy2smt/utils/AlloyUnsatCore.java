package edu.uiowa.alloy2smt.utils;

import com.fasterxml.jackson.annotation.JsonProperty;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.uiowa.smt.smtAst.SmtUnsatCore;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlRootElement;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

@XmlRootElement(name = "AlloyUnsatCore")
public class AlloyUnsatCore
{
  @XmlAttribute(name = "ranges")
  @JsonProperty("ranges")
  public List<Range> ranges = new ArrayList<>();

  public Set<Pos> getPositions()
  {
    return ranges.stream().map(r -> r.toPos()).collect(Collectors.toSet());
  }

  public static AlloyUnsatCore fromSmtUnsatCore(SmtUnsatCore smtUnsatCore) throws IOException
  {
    AlloyUnsatCore alloyUnsatCore = new AlloyUnsatCore();
    for (String json : smtUnsatCore.getCore())
    {
      Range range = Range.fromJson(json);
      alloyUnsatCore.ranges.add(range);
    }

    return alloyUnsatCore;
  }
}
