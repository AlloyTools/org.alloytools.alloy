package ca.uwaterloo.watform.core;

// everything must be static
public class DashOptions {


    public static String  dashModelLocation  = "";

    public static boolean isElectrum = false;
    public static boolean isTcmc = false;
    public static boolean isTraces = true;

    // remove these options since these are predicates
    public static boolean singleEventInput  = true; // predicate
    public static boolean reachability  = true; // predicate
    public static boolean enoughOperations  = true; // predicate


    public static boolean includeTrans = true; // for debugging
    //NAD other stuff that might be removed
    //public static boolean variablesUnchanged = true;

}
