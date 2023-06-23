package ca.uwaterloo.watform.dashtotla;


import java.util.List;

import ca.uwaterloo.watform.parser.*;

public class DashtoTLA 
{
    public static String translate(DashModule d)
    {
        StringBuilder things = new StringBuilder();

        List<String> trans = d.getAllTransNames();
        things.append("\nTransitions:");
        for(String s : trans)things.append("\n----\n").append(s);

        List<String> vars = d.getAllVarNames();
        things.append("\nVariables:");
        for(String s : vars)things.append("\n----\n").append(s);

        List<String> env_events = d.getAllEnvironmentalEventNames();
        things.append("\nEnvironmental events:");
        for(String s : env_events)things.append("\n----\n").append(s);

        List<String> events = d.getAllInternalEventNames();
        things.append("\nInternal events:");
        for(String s : events)things.append("\n----\n").append(s);

        System.out.print(d.toStringAlloy());

        return "\\*Hello World\n(*"+things.toString()+"*)";
    }
}
