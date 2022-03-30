package ca.uwaterloo.watform.parser;


public class DashOptions {

    public static String  outputDir          = "";
    public static String  dashModelLocation  = "";
    public static boolean isEnvEventModel    = false;
    public static boolean doneParsing        = false;
    public static boolean hasEvents          = false;
    public static boolean isDash             = false;
     
    public static boolean variablesUnchanged = true;
    public static boolean assumeSingleInput  = false;
    public static boolean generateSigAxioms  = false;
    public static boolean ctlModelChecking   = false;
    public static boolean reachabilityCheck   = false;
    public static boolean generateTraces   = true;
}
