/* 
 * For the util functions used many places
 */

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

public class DashUtilFcns {

	/* copied from https://stackoverflow.com/questions/7414667/identify-duplicates-in-a-list */
	public static <T> Set<T> findDuplicates(Collection<T> collection) {

		Set<T> duplicates = new LinkedHashSet<>();
		Set<T> uniques = new HashSet<>();

		for(T t : collection) 
		    if(!uniques.add(t)) 
		        duplicates.add(t);
		return duplicates;
	}

	public static <T> String strCommaList(List<T> ll) {
		StringJoiner sj = new StringJoiner(", ");
        ll.forEach(n -> sj.add(n.toString()));
        return sj.toString();		
	}
	public static <T> Set<T> listToSet(List<T> ll) {
		return ll.stream().collect(Collectors.toSet());
	}
	
	public static <T> List<T> setToList(Set<T> ll) {
		return new ArrayList<T>(ll);
	}
	
	public static void myprint(String s) {
		// debugging output
		System.out.println(s);
	}
	public static <T> List<T> newListWith(List<T> ll, T s) {
		List<T> x = new ArrayList<T>(ll);
		x.add(s);
		return x;
	}
	public static <T> String NoneStringIfNeeded(T x) {
		return ( (x == null) ? "none" : x.toString()) ;
	}

	public static void handleException(Exception e) {    
        e.printStackTrace(System.err);
        System.exit(1);
    }

	public static <T> T lastElement(List<T> ll) {
		return ll.get(ll.size() - 1 );
	}

    public static <T> List<T> allButLast(List<T> ll) {
    	if (ll.isEmpty()) return ll;
    	else return ll.subList(0,ll.size()-1);
    }
    // java's Collection.reverse doesn't work sometimes
    public static <T> List<T> reverse(List<T> ll) {
    	assert(!ll.isEmpty());
    	List<T> x = new ArrayList<T>();
    	for (int i=ll.size()-1;i>=0;i--) {
    		x.add(ll.get(i));
    	}
    	assert(x.size() == ll.size());
    	return x;
    }

    public static List<Integer> listOfInt(int start, int stop) {
    	assert(start <= stop);
    	List<Integer> x = new ArrayList<Integer>();
    	for (int i=start; i <= stop; i++) x.add(i);
    	return x;
    }
}