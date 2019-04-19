package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.smtAst.*;
import edu.uiowa.shared.CommandResult;
import edu.uiowa.shared.TestUtils;
import org.junit.Test;
import org.junit.jupiter.api.Assertions;

import java.util.*;

public class ArithmeticTests
{
    private int getInt(FunctionDefinition definition)
    {
        return getInt(definition.expression);
    }

    private int getInt(Expression expression)
    {
        UnaryExpression unary =  (UnaryExpression) expression;
        if(unary.getOP() == UnaryExpression.Op.EMPTYSET)
        {
            return 0; // zero is equivalent to an empty set
        }
        Assertions.assertEquals(UnaryExpression.Op.SINGLETON, unary.getOP());
        MultiArityExpression tuple =  (MultiArityExpression) unary.getExpression();
        Assertions.assertEquals(MultiArityExpression.Op.MKTUPLE, tuple.getOp());
        IntConstant constant = (IntConstant) tuple.getExpressions().get(0);
        return Integer.parseInt(constant.getValue());
    }

    private Set<Integer> getIntSet(FunctionDefinition definition)
    {
        return getIntSet(definition.getExpression());
    }

    private Set<Integer> getIntSet(Expression expression)
    {
        if(expression instanceof UnaryExpression)
        {
            return new HashSet<>(Arrays.asList(getInt(expression)));
        }
        BinaryExpression binary = (BinaryExpression) expression;
        Set<Integer> set = new HashSet<>();
        Assertions.assertEquals(BinaryExpression.Op.UNION, binary.getOp());
        set.addAll(getIntSet(binary.getLhsExpr()));
        set.addAll(getIntSet(binary.getRhsExpr()));
        return set;
    }
    
    @Test
    public void union() throws Exception
    {
        String alloy = "sig a in Int {} fact {a = 6 + 8}";
        List<CommandResult> commandResults = TestUtils.runCVC4(alloy);
        Assertions.assertEquals("sat", commandResults.get(0).result);
        FunctionDefinition a = TestUtils.getFunctionDefinition(commandResults.get(0), "this_a");
        Set<Integer> set = getIntSet(a);
        Assertions.assertEquals(set, new HashSet<>(Arrays.asList(6, 8)));
    }

    @Test
    public void singletons() throws Exception
    {
        String alloy =
                "sig a, b, c in Int {}\n" +
                "fact {\n" +
                "#a = 1\n" +
                "#b = 1\n" +
                "1 = 1\n" +
                "plus[a, b] = 2\n" +
                "plus[c, 0] = 2\n" +
                "}\n";
        List<CommandResult> commandResults = TestUtils.runCVC4(alloy);
        Assertions.assertTrue(commandResults.size() == 1);
        Assertions.assertEquals("sat", commandResults.get(0).result);
        FunctionDefinition a = TestUtils.getFunctionDefinition(commandResults.get(0), "this_a");
        FunctionDefinition b = TestUtils.getFunctionDefinition(commandResults.get(0), "this_b");
        FunctionDefinition c = TestUtils.getFunctionDefinition(commandResults.get(0), "this_c");

        int aValue = getInt(a);
        int bValue = getInt(b);
        int cValue = getInt(c);
        Assertions.assertEquals(2, aValue + bValue);
        Assertions.assertEquals(2, cValue);
    }

    @Test
    public void sets() throws Exception
    {
        String alloy =
                "sig a, b, c in Int {} \n" +
                "fact { \n" +
                "a = 1+2 \n" +
                "b = 4+6 \n" +
                "plus[a, b] = c\n" +
                "}";
        List<CommandResult> commandResults = TestUtils.runCVC4(alloy);
        Assertions.assertTrue(commandResults.size() == 1);
        Assertions.assertEquals("sat", commandResults.get(0).result);
        FunctionDefinition a = TestUtils.getFunctionDefinition(commandResults.get(0), "this_a");
        Set<Integer> aSet = getIntSet(a);
        Assertions.assertEquals(aSet, new HashSet<>(Arrays.asList(1, 2)));
        FunctionDefinition b = TestUtils.getFunctionDefinition(commandResults.get(0), "this_b");
        Set<Integer> bSet = getIntSet(b);
        Assertions.assertEquals(bSet, new HashSet<>(Arrays.asList(4, 6)));
        FunctionDefinition c = TestUtils.getFunctionDefinition(commandResults.get(0), "this_c");
        Set<Integer> cSet = getIntSet(c);
        Assertions.assertEquals(cSet, new HashSet<>(Arrays.asList(5, 7, 6, 8)));
    }

    @Test
    public void plusMinus() throws Exception
    {
        String alloy =
                "sig a, b, c in Int {} \n" +
                "fact { \n" +
                "plus[a, b] = c \n" +
                "minus[a,b] = c\n" +
                "}";
        List<CommandResult> commandResults = TestUtils.runCVC4(alloy);
        Assertions.assertTrue(commandResults.size() == 1);
        Assertions.assertEquals("sat", commandResults.get(0).result);
        FunctionDefinition b = TestUtils.getFunctionDefinition(commandResults.get(0), "this_b");
        Set<Integer> bSet = getIntSet(b);
        Assertions.assertEquals(bSet, new HashSet<>(Arrays.asList(0)));
    }

    @Test
    public void remainder() throws Exception
    {
        String alloy =
                "sig a, b, c in Int {} \n" +
                "fact { \n" +
                "#a = 2\n" +
                "8 in a\n" +
                "6 in a\n" +
                "#b = 1\n" +
                "rem[a,b] = c\n" +
                "}";
        List<CommandResult> commandResults = TestUtils.runCVC4(alloy);
        Assertions.assertTrue(commandResults.size() == 1);
        Assertions.assertEquals("sat", commandResults.get(0).result);
        FunctionDefinition mod = TestUtils.getFunctionDefinition(commandResults.get(0), Alloy2SmtTranslator.mod);
    }

    @Test
    public void unsatPlusMinus() throws Exception
    {
        String alloy =
                "sig a, b, c, d in Int {}\n" +
                "fact add{plus[a,b] = c + d}\n" +
                "fact subtract{minus[a,b] = c - d}\n" +
                "fact notEqual{a != c and b != d}\n" +
                "fact nonzero {a > 0 and b > 0 and c > 0 and d > 0}\n";
        List<CommandResult> commandResults = TestUtils.runCVC4(alloy);
        Assertions.assertEquals("unsat", commandResults.get(0).result);
    }

    @Test
    public void sum() throws Exception
    {
        String alloy = "sig a, b, c in Int {}\n" +
                "fact {sum [a] = 1  and sum[b] = 2 and sum[c] = 3}";

        List<CommandResult> commandResults = TestUtils.runCVC4(alloy);
        Assertions.assertTrue(commandResults.size() == 1);
        Assertions.assertEquals("sat", commandResults.get(0).result);
        FunctionDefinition a = TestUtils.getFunctionDefinition(commandResults.get(0), "this_a");
        Set<Integer> aSet = getIntSet(a);
        Assertions.assertEquals(aSet, new HashSet<>(Arrays.asList(1)));

        FunctionDefinition b = TestUtils.getFunctionDefinition(commandResults.get(0), "this_b");
        Set<Integer> bSet = getIntSet(b);
        Assertions.assertEquals(bSet, new HashSet<>(Arrays.asList(2)));

        FunctionDefinition c = TestUtils.getFunctionDefinition(commandResults.get(0), "this_c");
        Set<Integer> cSet = getIntSet(c);
        Assertions.assertEquals(cSet, new HashSet<>(Arrays.asList(3)));
    }

    @Test
    public void sumUnsat() throws Exception
    {
        String alloy = "sig a, b, c in Int {}\n" +
                "fact {sum [a] = 1  and sum[b] = 2 and sum[c] = 3 and #c = 3}";

        List<CommandResult> commandResults = TestUtils.runCVC4(alloy);
        Assertions.assertTrue(commandResults.size() == 1);
        Assertions.assertEquals("unsat", commandResults.get(0).result);
    }
}
