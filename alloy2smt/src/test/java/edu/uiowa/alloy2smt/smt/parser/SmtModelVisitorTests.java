package edu.uiowa.alloy2smt.smt.parser;

import edu.uiowa.alloy2smt.smt.smtAst.FunctionDefinition;
import edu.uiowa.alloy2smt.smt.smtAst.SmtModel;
import edu.uiowa.alloy2smt.smt.parser.antlr.SmtLexer;
import edu.uiowa.alloy2smt.smt.parser.antlr.SmtParser;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

class SmtModelVisitorTests
{

    SmtModel parseModel(String model)
    {
        CharStream charStream = CharStreams.fromString(model);

        SmtLexer lexer = new SmtLexer(charStream);
        CommonTokenStream tokenStream = new CommonTokenStream(lexer);
        SmtParser parser = new SmtParser(tokenStream);

        ParseTree tree =  parser.model();
        SmtModelVisitor visitor = new SmtModelVisitor();
        SmtModel smtModel = (SmtModel) visitor.visit(tree);
        return  smtModel;
    }

    @Test
    void model1()
    {
        String model =
                "(model\n" +
                "; cardinality of Atom is 1\n" +
                "(declare-sort Atom 0)\n" +
                "; rep: @uc_Atom_0\n" +
                "(declare-sort UnaryIntTup 0)\n" +
                "(declare-sort BinaryIntTup 0)\n" +
                "(declare-sort TernaryIntTup 0)\n" +
                "(define-fun value_of_unaryIntTup ((BOUND_VARIABLE_448 UnaryIntTup)) (Tuple Int) (mkTuple 0))\n" +
                "(define-fun value_of_binaryIntTup ((BOUND_VARIABLE_457 BinaryIntTup)) (Tuple Int Int) (mkTuple 0 0))\n" +
                "(define-fun value_of_ternaryIntTup ((BOUND_VARIABLE_466 TernaryIntTup)) (Tuple Int Int Int) (mkTuple 0 0 0))\n" +
                "(define-fun atomNone () (Set (Tuple Atom)) (as emptyset (Set (Tuple Atom))))\n" +
                "(define-fun atomUniv () (Set (Tuple Atom)) (as emptyset (Set (Tuple Atom))))\n" +
                "(define-fun atomIden () (Set (Tuple Atom Atom)) (as emptyset (Set (Tuple Atom Atom))))\n" +
                ")";

        SmtModel smtModel = parseModel(model);
        Assertions.assertEquals(4, smtModel.getSorts().size());
        Assertions.assertEquals(6, smtModel.getFunctions().size());

        FunctionDefinition atomUniv = (FunctionDefinition) smtModel.getFunctions().stream()
                .filter(function -> function.getName().equals("atomUniv")).findFirst().get();

        Assertions.assertTrue(atomUniv.expression != null);
    }

    @Test
    void model2()
    {
        String model =
                "(model\n" +
                        "; cardinality of Atom is 1\n" +
                        "(declare-sort Atom 0)\n" +
                        "; rep: @uc_Atom_0\n" +
                        "(declare-sort UnaryIntTup 0)\n" +
                        "(declare-sort BinaryIntTup 0)\n" +
                        "(declare-sort TernaryIntTup 0)\n" +
                        "(define-fun value_of_unaryIntTup ((BOUND_VARIABLE_1790 UnaryIntTup)) (Tuple Int) (mkTuple 0))\n" +
                        "(define-fun value_of_binaryIntTup ((BOUND_VARIABLE_1799 BinaryIntTup)) (Tuple Int Int) (mkTuple 0 0))\n" +
                        "(define-fun value_of_ternaryIntTup ((BOUND_VARIABLE_1808 TernaryIntTup)) (Tuple Int Int Int) (mkTuple 0 0 0))\n" +
                        "(define-fun atomNone () (Set (Tuple Atom)) (as emptyset (Set (Tuple Atom))))\n" +
                        "(define-fun atomUniv () (Set (Tuple Atom)) (singleton (mkTuple @uc_Atom_0)))\n" +
                        "(define-fun atomIden () (Set (Tuple Atom Atom)) (singleton (mkTuple @uc_Atom_0 @uc_Atom_0)))\n" +
                        "(define-fun this_Object () (Set (Tuple Atom)) (singleton (mkTuple @uc_Atom_0)))\n" +
                        "(define-fun this_Dir () (Set (Tuple Atom)) (singleton (mkTuple @uc_Atom_0)))\n" +
                        "(define-fun this_Root () (Set (Tuple Atom)) (singleton (mkTuple @uc_Atom_0)))\n" +
                        "(define-fun this_File () (Set (Tuple Atom)) (as emptyset (Set (Tuple Atom))))\n" +
                        "(define-fun this_Dir_contents () (Set (Tuple Atom Atom)) (singleton (mkTuple @uc_Atom_0 @uc_Atom_0)))\n" +
                        "(define-fun _x1 () Atom @uc_Atom_0)\n" +
                        ")";

        SmtModel smtModel = parseModel(model);
        Assertions.assertEquals(4, smtModel.getSorts().size());
        Assertions.assertEquals(12, smtModel.getFunctions().size());
    }

    @Test
    void model3()
    {
        String model =
                "(model\n" +
                        "; cardinality of Atom is 1\n" +
                        "(declare-sort Atom 0)\n" +
                        "; rep: @uc_Atom_0\n" +
                        "; cardinality of UnaryIntTup is 1\n" +
                        "(declare-sort UnaryIntTup 0)\n" +
                        "; rep: @uc_UnaryIntTup_0\n" +
                        "(declare-sort BinaryIntTup 0)\n" +
                        "(declare-sort TernaryIntTup 0)\n" +
                        "(define-fun value_of_unaryIntTup ((BOUND_VARIABLE_692 UnaryIntTup)) (Tuple Int) (mkTuple 5))\n" +
                        "(define-fun value_of_binaryIntTup ((BOUND_VARIABLE_701 BinaryIntTup)) (Tuple Int Int) (mkTuple 0 0))\n" +
                        "(define-fun value_of_ternaryIntTup ((BOUND_VARIABLE_710 TernaryIntTup)) (Tuple Int Int Int) (mkTuple 0 0 0))\n" +
                        "(define-fun atomNone () (Set (Tuple Atom)) (as emptyset (Set (Tuple Atom))))\n" +
                        "(define-fun atomUniv () (Set (Tuple Atom)) (as emptyset (Set (Tuple Atom))))\n" +
                        "(define-fun atomIden () (Set (Tuple Atom Atom)) (as emptyset (Set (Tuple Atom Atom))))\n" +
                        "(define-fun this_A () (Set (Tuple Int)) (singleton (mkTuple 0)))\n" +
                        "(define-fun this_B () (Set (Tuple Int)) (singleton (mkTuple 0)))\n" +
                        "(define-fun PLUS () (Set (Tuple Int Int Int)) (singleton (mkTuple 0 0 5)))\n" +
                        ")";
        SmtModel smtModel = parseModel(model);
        Assertions.assertEquals(4, smtModel.getSorts().size());
        Assertions.assertEquals(9, smtModel.getFunctions().size());
    }

    @Test
    void model4()
    {
        String model =
                "(model\n" +
                "; cardinality of Atom is 1\n" +
                "(declare-sort Atom 0)\n" +
                "; rep: @uc_Atom_0\n" +
                "; cardinality of UnaryIntTup is 2\n" +
                "(declare-sort UnaryIntTup 0)\n" +
                "; rep: @uc_UnaryIntTup_0\n" +
                "; rep: @uc_UnaryIntTup_1\n" +
                "(declare-sort BinaryIntTup 0)\n" +
                "(declare-sort TernaryIntTup 0)\n" +
                "(define-fun value_of_unaryIntTup ((BOUND_VARIABLE_744 UnaryIntTup)) (Tuple Int) (ite (= @uc_UnaryIntTup_1 BOUND_VARIABLE_744) (mkTuple (- 1)) (mkTuple 0)))\n" +
                "(define-fun value_of_binaryIntTup ((BOUND_VARIABLE_757 BinaryIntTup)) (Tuple Int Int) (mkTuple 0 0))\n" +
                "(define-fun value_of_ternaryIntTup ((BOUND_VARIABLE_766 TernaryIntTup)) (Tuple Int Int Int) (mkTuple 0 0 0))\n" +
                "(define-fun atomNone () (Set (Tuple Atom)) (as emptyset (Set (Tuple Atom))))\n" +
                "(define-fun atomUniv () (Set (Tuple Atom)) (as emptyset (Set (Tuple Atom))))\n" +
                "(define-fun atomIden () (Set (Tuple Atom Atom)) (as emptyset (Set (Tuple Atom Atom))))\n" +
                "(define-fun this_A0 () (Set (Tuple Int)) (singleton (mkTuple 0)))\n" +
                "(define-fun this_A1 () (Set (Tuple Int)) (singleton (mkTuple (- 1))))\n" +
                "(define-fun this_A2 () (Set (Tuple Int)) (as emptyset (Set (Tuple Int))))\n" +
                ")";

        SmtModel smtModel = parseModel(model);
        Assertions.assertEquals(4, smtModel.getSorts().size());
        Assertions.assertEquals(9, smtModel.getFunctions().size());
    }

    @Test
    void model5()
    {
        String model =
                "(model\n" +
                        "(define-fun ord_IntMap ((BOUND_VARIABLE_6486 Atom)) Int (ite (= @uc_Atom_3 BOUND_VARIABLE_6486) 1 (ite (= @uc_Atom_0 BOUND_VARIABLE_6486) 2 0)))\n" +
                ")";

        SmtModel smtModel = parseModel(model);
        Assertions.assertEquals(0, smtModel.getSorts().size());
        Assertions.assertEquals(1, smtModel.getFunctions().size());
    }

    @Test
    void model6()
    {
        String model =
                "(model\n" +
                        "; cardinality of Atom is 4\n" +
                        "(declare-sort Atom 0)\n" +
                        "; rep: @uc_Atom_0\n" +
                        "; rep: @uc_Atom_1\n" +
                        "; rep: @uc_Atom_2\n" +
                        "; rep: @uc_Atom_3\n" +
                        "(declare-sort UnaryIntTup 0)\n" +
                        "(declare-sort BinaryIntTup 0)\n" +
                        "(declare-sort TernaryIntTup 0)\n" +
                        "(define-fun value_of_unaryIntTup ((BOUND_VARIABLE_6461 UnaryIntTup)) (Tuple Int) (mkTuple 0))\n" +
                        "(define-fun value_of_binaryIntTup ((BOUND_VARIABLE_6470 BinaryIntTup)) (Tuple Int Int) (mkTuple 0 0))\n" +
                        "(define-fun value_of_ternaryIntTup ((BOUND_VARIABLE_6479 TernaryIntTup)) (Tuple Int Int Int) (mkTuple 0 0 0))\n" +
                        "(define-fun atomNone () (Set (Tuple Atom)) (as emptyset (Set (Tuple Atom))))\n" +
                        "(define-fun atomUniv () (Set (Tuple Atom)) (union (union (union (singleton (mkTuple @uc_Atom_0)) (singleton (mkTuple @uc_Atom_2))) (singleton (mkTuple @uc_Atom_3))) (singleton (mkTuple @uc_Atom_1))))\n" +
                        "(define-fun atomIden () (Set (Tuple Atom Atom)) (union (union (union (singleton (mkTuple @uc_Atom_3 @uc_Atom_3)) (singleton (mkTuple @uc_Atom_2 @uc_Atom_2))) (singleton (mkTuple @uc_Atom_1 @uc_Atom_1))) (singleton (mkTuple @uc_Atom_0 @uc_Atom_0))))\n" +
                        "(define-fun this_A () (Set (Tuple Atom)) (union (union (singleton (mkTuple @uc_Atom_0)) (singleton (mkTuple @uc_Atom_2))) (singleton (mkTuple @uc_Atom_3))))\n" +
                        "(define-fun this_A0 () (Set (Tuple Atom)) (singleton (mkTuple @uc_Atom_2)))\n" +
                        "(define-fun this_A1 () (Set (Tuple Atom)) (singleton (mkTuple @uc_Atom_3)))\n" +
                        "(define-fun this_A2 () (Set (Tuple Atom)) (singleton (mkTuple @uc_Atom_0)))\n" +
                        "(define-fun ord_Ord () (Set (Tuple Atom)) (singleton (mkTuple @uc_Atom_1)))\n" +
                        "(define-fun ord_Ord_First () (Set (Tuple Atom Atom)) (singleton (mkTuple @uc_Atom_1 @uc_Atom_2)))\n" +
                        "(define-fun ord_Ord_Next () (Set (Tuple Atom Atom Atom)) (union (singleton (mkTuple @uc_Atom_1 @uc_Atom_3 @uc_Atom_0)) (singleton (mkTuple @uc_Atom_1 @uc_Atom_2 @uc_Atom_3))))\n" +
                        "(define-fun ord_IntMap ((BOUND_VARIABLE_6486 Atom)) Int (ite (= @uc_Atom_3 BOUND_VARIABLE_6486) 1 (ite (= @uc_Atom_0 BOUND_VARIABLE_6486) 2 0)))\n" +
                        "(define-fun _x1 () Atom @uc_Atom_1)\n" +
                        "(define-fun _a1 () Atom @uc_Atom_2)\n" +
                        "(define-fun ord_first () (Set (Tuple Atom)) (singleton (mkTuple @uc_Atom_2)))\n" +
                        "(define-fun _a2 () Atom @uc_Atom_0)\n" +
                        "(define-fun ord_last () (Set (Tuple Atom)) (singleton (mkTuple @uc_Atom_0)))\n" +
                        "(define-fun ord_next () (Set (Tuple Atom Atom)) (union (singleton (mkTuple @uc_Atom_3 @uc_Atom_0)) (singleton (mkTuple @uc_Atom_2 @uc_Atom_3))))\n" +
                        "(define-fun ord_prev () (Set (Tuple Atom Atom)) (union (singleton (mkTuple @uc_Atom_3 @uc_Atom_2)) (singleton (mkTuple @uc_Atom_0 @uc_Atom_3))))\n" +
                        ")";

        SmtModel smtModel = parseModel(model);
        FunctionDefinition atomUniv = (FunctionDefinition) smtModel.getFunctions()
                .stream()
                .filter(function -> function.getName().equals("atomUniv"))
                .findFirst().get();
        Assertions.assertEquals("(union (union (union (singleton (mkTuple @uc_Atom_0)) (singleton (mkTuple @uc_Atom_2))) (singleton (mkTuple @uc_Atom_3))) (singleton (mkTuple @uc_Atom_1)))",
                atomUniv.expression.toString());
    }

    @Test
    void model17()
    {
        String model =
                "(model\n" +
                        "; cardinality of Atom is 1\n" +
                        "(declare-sort Atom 0)\n" +
                        "; rep: @uc_Atom_0\n" +
                        "; cardinality of UnaryIntTup is 3\n" +
                        "(declare-sort UnaryIntTup 0)\n" +
                        "; rep: @uc_UnaryIntTup_0\n" +
                        "; rep: @uc_UnaryIntTup_1\n" +
                        "; rep: @uc_UnaryIntTup_2\n" +
                        "(declare-sort BinaryIntTup 0)\n" +
                        "; cardinality of TernaryIntTup is 7\n" +
                        "(declare-sort TernaryIntTup 0)\n" +
                        "; rep: @uc_TernaryIntTup_0\n" +
                        "; rep: @uc_TernaryIntTup_1\n" +
                        "; rep: @uc_TernaryIntTup_2\n" +
                        "; rep: @uc_TernaryIntTup_3\n" +
                        "; rep: @uc_TernaryIntTup_4\n" +
                        "; rep: @uc_TernaryIntTup_5\n" +
                        "; rep: @uc_TernaryIntTup_6\n" +
                        "(define-fun value_of_unaryIntTup ((BOUND_VARIABLE_15814 UnaryIntTup)) (Tuple Int) (ite (= @uc_UnaryIntTup_2 BOUND_VARIABLE_15814) (mkTuple 3) (ite (= @uc_UnaryIntTup_0 BOUND_VARIABLE_15814) (mkTuple 2) (mkTuple 0))))\n" +
                        "(define-fun value_of_binaryIntTup ((BOUND_VARIABLE_15833 BinaryIntTup)) (Tuple Int Int) (mkTuple 0 0))\n" +
                        "(define-fun value_of_ternaryIntTup ((BOUND_VARIABLE_15844 TernaryIntTup)) (Tuple Int Int Int) (ite (= @uc_TernaryIntTup_6 BOUND_VARIABLE_15844) (mkTuple 3 3 0) (ite (= @uc_TernaryIntTup_4 BOUND_VARIABLE_15844) (mkTuple 3 0 3) (ite (= @uc_TernaryIntTup_3 BOUND_VARIABLE_15844) (mkTuple 2 0 2) (ite (= @uc_TernaryIntTup_2 BOUND_VARIABLE_15844) (mkTuple 2 2 0) (ite (= @uc_TernaryIntTup_1 BOUND_VARIABLE_15844) (mkTuple 0 0 0) (ite (= @uc_TernaryIntTup_0 BOUND_VARIABLE_15844) (mkTuple 0 2 2) (mkTuple 0 3 3))))))))\n" +
                        "(define-fun atomNone () (Set (Tuple Atom)) (as emptyset (Set (Tuple Atom))))\n" +
                        "(define-fun atomUniv () (Set (Tuple Atom)) (as emptyset (Set (Tuple Atom))))\n" +
                        "(define-fun atomIden () (Set (Tuple Atom Atom)) (as emptyset (Set (Tuple Atom Atom))))\n" +
                        "(define-fun this_a () (Set (Tuple Int)) (singleton (mkTuple 2)))\n" +
                        "(define-fun this_b () (Set (Tuple Int)) (singleton (mkTuple 3)))\n" +
                        "(define-fun this_c () (Set (Tuple Int)) (singleton (mkTuple 3)))\n" +
                        "(define-fun this_d () (Set (Tuple Int)) (singleton (mkTuple 2)))\n" +
                        "(define-fun PLUS () (Set (Tuple Int Int Int)) (union (union (union (union (union (union (singleton (mkTuple 0 0 0)) (singleton (mkTuple 2 0 2))) (singleton (mkTuple 0 2 2))) (singleton (mkTuple 2 3 2))) (singleton (mkTuple 3 0 3))) (singleton (mkTuple 2 3 3))) (singleton (mkTuple 0 3 3))))\n" +
                        "(define-fun MINUS () (Set (Tuple Int Int Int)) (union (union (union (union (union (singleton (mkTuple 0 0 0)) (singleton (mkTuple 2 2 0))) (singleton (mkTuple 2 0 2))) (singleton (mkTuple 3 3 0))) (singleton (mkTuple 3 0 3))) (singleton (mkTuple 2 3 3))))\n" +
                        ")";

        SmtModel smtModel = parseModel(model);
    }
}