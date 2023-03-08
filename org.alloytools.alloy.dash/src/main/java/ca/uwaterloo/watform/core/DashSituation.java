package ca.uwaterloo.watform.core;

import java.util.*;

// everything must be static
public class DashSituation {

    // we need a little bit of knowledge of the state of the process
    // open statements have to be done before anything else in an
    // Alloy file, but we don't know how many buffers we have
    // so we have to run parsing once to count buffers
    // and then a second time with the appropriate open statements
    // we don't want to put this state within the DashModule because
    // then we'd have to pass the dash module into the parser
    // which isn't available at the parseFromFile in DashUtil (copied from CompUtil)
    // so we set this after the first parse run
    // and check it during the second parse run 
    public static boolean haveCountedBuffers = false;
    // buffer elements in order of buffers
    public static List<String> bufferElements = new ArrayList<String>();
    // we will need more here to know the names of the elements
    // of the buffers for the open statements
}