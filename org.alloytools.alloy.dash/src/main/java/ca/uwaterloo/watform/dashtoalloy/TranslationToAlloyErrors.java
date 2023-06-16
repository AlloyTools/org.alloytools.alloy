/* 
 * All the errors that can be thrown in Dash code
 */

package ca.uwaterloo.watform.dashtoalloy;

import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.ast.Expr;

public class TranslationToAlloyErrors {

    public static void Unsupported(Expr e) throws Err {
        throw new ErrorSyntax("Unsupported: " + e.toString());
    }
}