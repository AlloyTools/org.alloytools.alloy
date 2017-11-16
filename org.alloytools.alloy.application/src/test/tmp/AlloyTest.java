package tmp;

import java.util.logging.Level;
import java.util.logging.Logger;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

public class AlloyTest {

    public static void main(String[] args) throws Exception {
        A4Reporter rep = new A4Reporter();
        
        Module world = CompUtil.parseEverything_fromFile(rep, null, "/home/aleks/mvc.als");
        A4Options options = new A4Options();
        options.solver = A4Options.SatSolver.SAT4J;
        options.skolemDepth = 1;
        
        for (Command command : world.getAllCommands()) {
            A4Solution ans = null;
            try {
                ans = TranslateAlloyToKodkod.execute_commandFromBook(rep, world.getAllReachableSigs(), command, options);
                System.out.println(ans);
            } catch (Err ex) {
                Logger.getLogger(AlloyTest.class.getName()).log(Level.SEVERE, null, ex);
            }
        }
    }
    
}
