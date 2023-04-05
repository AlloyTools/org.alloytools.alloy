package ca.uwaterloo.watform.core;

import java.util.StringJoiner;
import java.util.List;
import java.util.Collection;
import java.util.Set;
import java.util.Arrays;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.stream.Collectors;


public class DashFQN {

	// used for translation to Alloy
	//NAD TODO this should match the qualChar used in parsing for vars and state names
	private static String inputQualChar = "/";
	private static String outputQualChar = "_";

	public static String convertFQN(String n) {
		return n.replace(inputQualChar, outputQualChar);
	}
	public static Boolean alreadyFQN(String n) {
		return n.contains(inputQualChar);
	}
	public static String fqn(List<String> pth) {
		if (pth.isEmpty()) return null; // for root
		StringJoiner sj = new StringJoiner(inputQualChar);
        pth.forEach(n -> sj.add(n));
        return sj.toString();
	}
	public static String fqn(String s1,String s2) {
		String q = new String(s1);
		q += inputQualChar;
		q += s2;
        return q;
	}
	public static String fqn(List<String> pth, String name) {
		if (alreadyFQN(name)) 
			//return name.replace(inputQualChar,outputQualChar);
			return name;
		else {
			StringJoiner sj = new StringJoiner(inputQualChar);
    	    pth.forEach(n -> sj.add(n));
        	sj.add(name);
        	return sj.toString();
        }
	}
	public static String fqn(List<String> pth, String parent, String child) {
		if (alreadyFQN(child)) 
			//return child.replace(inputQualChar,outputQualChar);
			return child;
		else {
			StringJoiner sj = new StringJoiner(inputQualChar);
	        pth.forEach(n -> sj.add(n));
	        sj.add(parent);
	        sj.add(child);
	        return sj.toString();
	    }
	}
	public static List<String> splitFQN(String fqn) {
		return Arrays.asList(fqn.split(inputQualChar));
	}
	public static String chopNameFromFQN(String fqn) {
		// this is from an output FQN
		return DashUtilFcns.last(splitFQN(fqn));
	}
	// can't just take longest prefix because states may have similar names
	// such as Bit1 and Bit2
	public static String longestCommonFQN(String a, String b) {
		List<String> aSplit = splitFQN(a);
		List<String> bSplit = splitFQN(b);
		String result = new String();
    	int minLength = Math.min(aSplit.size(), bSplit.size());
    	int i = 0;
        while (i < minLength && aSplit.get(i).equals(bSplit.get(i))) i++;
    	return fqn(aSplit.subList(0,i));
	}
	public static List<String> allPrefixes(String fqn) {
		List<String> prefixes = new ArrayList<String>();
		// not including state itself
		List<String> splitfqn = splitFQN(fqn);
		for (int i=0;i < splitfqn.size()-1; i++) {
			StringJoiner sj = new StringJoiner(inputQualChar);
			for (int j=0;j<=i;j++) {
				sj.add(splitfqn.get(j));				
			}
			prefixes.add(sj.toString());
		}
		return prefixes;
	}
	/* ances: A/B/C dest: A/B/C/D/E returns A/B/C/D */
	public static String getChildOfContextAncesOfDest(String ances, String dest) {
		if (dest.startsWith(ances)) 
			// by going to ances, we are adding +1
			return fqn(splitFQN(dest).subList(0,splitFQN(ances).size()));
		else { DashErrors.ancesNotPrefix(ances,dest); return null; }
	}
}