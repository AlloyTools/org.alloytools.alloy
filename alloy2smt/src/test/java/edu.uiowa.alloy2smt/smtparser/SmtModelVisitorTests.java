package edu.uiowa.alloy2smt.smtparser;

import edu.uiowa.alloy2smt.smtAst.FunctionDefinition;
import edu.uiowa.alloy2smt.smtAst.SmtModel;
import edu.uiowa.alloy2smt.smtparser.antlr.SmtLexer;
import edu.uiowa.alloy2smt.smtparser.antlr.SmtParser;
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
        Assertions.assertEquals(6, smtModel.getFunctionDefinitions().size());

        FunctionDefinition atomUniv = smtModel.getFunctionDefinitions().stream()
                .filter(function -> function.funcName.equals("atomUniv")).findFirst().get();

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
        Assertions.assertEquals(12, smtModel.getFunctionDefinitions().size());
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
        Assertions.assertEquals(9, smtModel.getFunctionDefinitions().size());
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
        Assertions.assertEquals(9, smtModel.getFunctionDefinitions().size());
    }
}