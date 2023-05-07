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
	private static String internalQualChar = inputQualChar;
	private static String outputQualChar = "_";

	// to create Alloy output
	public static String translateFQN(String n) {
		return n.replace(internalQualChar, outputQualChar);
	}
	
	// testing inputs from parsing 
	public static Boolean isFQN(String n) {
		return n.contains(inputQualChar);
	}

	// creating FQNs from inputs --------------------------

	public static String fqn(String s1,String s2) {
		String q = new String(s1);
		q += internalQualChar;
		q += s2;
        return q;
	}
	// not really needed unless we change it so that
	// inputQualChar != internal QualChar
	public static String fqn(String n) {
		return n.replace(inputQualChar, internalQualChar);
	}
	public static String fqn(List<String> pth) {
		if (pth.isEmpty()) return null; // for root
		StringJoiner sj = new StringJoiner(internalQualChar);
        pth.forEach(n -> sj.add(fqn(n)));
        return sj.toString();
	}

	public static String fqn(List<String> pth, String name) {
		if (isFQN(name)) 
			return fqn(name);
		else {
			StringJoiner sj = new StringJoiner(internalQualChar);
    	    pth.forEach(n -> sj.add(fqn(n)));
        	sj.add(fqn(name));
        	return sj.toString();
        }
	}
	public static String fqn(List<String> pth, String parent, String child) {
		if (isFQN(child)) 
			//return child.replace(inputQualChar,outputQualChar);
			return fqn(child);
		else {
			StringJoiner sj = new StringJoiner(internalQualChar);
	        pth.forEach(n -> sj.add(fqn(n)));
	        sj.add(fqn(parent));
	        sj.add(fqn(child));
	        return sj.toString();
	    }
	}

	// operations on FQNs
	public static List<String> splitFQN(String fqn) {
		return Arrays.asList(fqn.split(internalQualChar));
	}
	public static String chopNameFromFQN(String fqn) {
		// this is from an output FQN
		return DashUtilFcns.lastElement(splitFQN(fqn));
	}
	// useful for getting parent state of a trans/event decl, etc.
	public static String chopPrefixFromFQN(String fqn) {
		List<String> s = splitFQN(fqn);
		if (s.size() < 2) { DashErrors.chopPrefixFromFQNwithNoPrefix(fqn); return null; }
		else return fqn(DashUtilFcns.allButLast(splitFQN(fqn)));
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
	// include this fqn
	public static List<String> allPrefixes(String fqn) {
		List<String> prefixes = new ArrayList<String>();
		List<String> splitfqn = splitFQN(fqn);
		for (int i=0;i < splitfqn.size(); i++) {
			StringJoiner sj = new StringJoiner(internalQualChar);
			for (int j=0;j<=i;j++) {
				sj.add(splitfqn.get(j));				
			}
			prefixes.add(sj.toString());
		}
		return prefixes;
	}
	/*
		suffix("A/B/C/x", "C/x") is true
		suffix("A/B/C/x", "x") is true
		suffix("x","x") is true
		suffix("A/B/xyz", "yz") is false
	*/
	public static boolean suffix(String a, String b) {
		//System.out.println(a);
		//System.out.println(b);
		if (a.endsWith(b)) {
			int x = a.lastIndexOf(b);
			//System.out.println(x);
			if (x != -1) {
				if (x == 0) return true;
				//System.out.println(a.charAt(x-1));
				if (a.charAt(x-1) == internalQualChar.charAt(0)) return true;
			}
		}
		return false;
	}
	/* ances: A/B/C dest: A/B/C/D/E returns A/B/C/D */
	public static String getChildOfContextAncesOfDest(String ances, String dest) {
		if (dest.equals(ances)) return dest;
		else if (dest.startsWith(ances)) 
			// dest must be longer than ances
			return fqn(splitFQN(dest).subList(0,splitFQN(ances).size()+1));
		else { DashErrors.ancesNotPrefix(ances,dest); return null; }
	}
}