package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.Utils;
import edu.uiowa.alloy2smt.smtAst.FunctionDefinition;
import edu.uiowa.alloy2smt.smtAst.IntConstant;
import edu.uiowa.alloy2smt.smtAst.MultiArityExpression;
import edu.uiowa.alloy2smt.smtAst.UnaryExpression;
import edu.uiowa.shared.CommandResult;
import edu.uiowa.shared.Cvc4Task;
import org.junit.Test;
import org.junit.jupiter.api.Assertions;
import java.util.List;

public class ArithmeticTests
{
    @Test
    public void simple() throws Exception
    {
        String alloy =
                "sig a, b, c in Int {}\n" +
                "fact {\n" +
                "#a = 1\n" +
                "#b = 1\n" +
                "plus[a, b] = 2\n" +
                "plus[c, 0] = 2\n" +
                "}\n";
        Translation translation = Utils.translate(alloy);
        Cvc4Task task = new Cvc4Task();
        List<CommandResult> commandResults =  task.run(translation);
        Assertions.assertTrue(commandResults.size() == 1);
        Assertions.assertEquals("sat", commandResults.get(0).result);
        String cName = "this_c";
        FunctionDefinition c = (FunctionDefinition) commandResults.get(0).smtModel
                .getFunctions().stream()
                .filter(f -> f.getName().equals(cName)).findFirst().get();
        UnaryExpression unary =  (UnaryExpression) c.expression;
        Assertions.assertEquals(UnaryExpression.Op.SINGLETON, unary.getOP());
        MultiArityExpression tuple =  (MultiArityExpression) unary.getExpression();
        Assertions.assertEquals(MultiArityExpression.Op.MKTUPLE, tuple.getOp());
        IntConstant constant = (IntConstant) tuple.getExpressions().get(0);
        int cValue = Integer.parseInt(constant.getValue());
        Assertions.assertEquals(2, cValue);
    }

    @Test
    public void testPlusMinus()
    {
        String alloy =
                "sig a, b, c, d in Int {}\n" +
                "fact add{plus[a,b] = c + d}\n" +
                "fact subtract{minus[a,b] = c - d}\n" +
                "fact notEqual{a != c and b != d}\n" +
                "fact nonzero {a > 0 and b > 0 and c > 0 and d > 0}\n";
        Translation translation = Utils.translate(alloy);

        Assertions.assertTrue(translation.getSmtScript().contains(
                "(declare-fun intUniv"));
    }
}
