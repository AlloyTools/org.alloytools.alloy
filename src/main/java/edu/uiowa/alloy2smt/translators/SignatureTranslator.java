package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.ast.Sig;
import edu.uiowa.alloy2smt.Utils;
import edu.uiowa.alloy2smt.smtAst.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class SignatureTranslator
{

    private final Alloy2SMTTranslator translator;
    private final FieldTranslator fieldTranslator;

    public SignatureTranslator(Alloy2SMTTranslator translator)
    {
        this.translator         = translator;
        this.fieldTranslator    = new FieldTranslator(translator);
    }

    private void translateSignatureHierarchies()
    {
        for (Sig sig: translator.topLevelSigs)
        {
            Sig.PrimSig primSig = (Sig.PrimSig) sig;
            translateDisjointSignatures(primSig);
            if(primSig.isAbstract != null)
            {
                SafeList<Sig.PrimSig> children = primSig.children();
                if(children.size() == 1)
                {
                    Expression left        = translator.signaturesMap.get(sig).getConstantExpr();
                    Expression          right       = translator.signaturesMap.get(children.get(0)).getConstantExpr();
                    BinaryExpression equality    = new BinaryExpression(left, BinaryExpression.Op.EQ, right);
                    translator.smtProgram.addAssertion(new Assertion(equality));
                }
                else if(children.size() > 1)
                {

                    Expression          left        = translator.signaturesMap.get(children.get(0)).getConstantExpr();
                    Expression          right       = translator.signaturesMap.get(children.get(1)).getConstantExpr();
                    BinaryExpression    union       = new BinaryExpression(left, BinaryExpression.Op.UNION, right);

                    for(int i = 2; i < children.size(); i++)
                    {
                        Expression      expression  = translator.signaturesMap.get(children.get(i)).getConstantExpr();
                        union                       = new BinaryExpression(union, BinaryExpression.Op.UNION, expression);
                    }

                    Expression          leftExpr    = translator.signaturesMap.get(sig).getConstantExpr();
                    BinaryExpression    equality    = new BinaryExpression(leftExpr, BinaryExpression.Op.EQ, union);
                    translator.smtProgram.addAssertion(new Assertion(equality));
                }
            }
        }
    }

    private void translateDisjointSignatures(Sig.PrimSig primSig)
    {
        for (int i = 0; i < primSig.children().size(); i++)
        {
            Expression      left    = translator.signaturesMap.get(primSig.children().get(i)).getConstantExpr();

            UnaryExpression emptySet   = new UnaryExpression(UnaryExpression.Op.EMPTYSET, translator.signaturesMap.get(primSig.children().get(i)).getOutputSort());

            for (int j = i + 1 ; j < primSig.children().size(); j++)
            {
                Expression          right       = translator.signaturesMap.get(primSig.children().get(j)).getConstantExpr();
                BinaryExpression    disjoint    = new BinaryExpression(left, BinaryExpression.Op.INTERSECTION, right);

                BinaryExpression    equality    = new BinaryExpression(disjoint, BinaryExpression.Op.EQ, emptySet);
                translator.smtProgram.addAssertion(new Assertion(equality));
            }
        }
    }

    private void collectReachableSigs()
    {
        translator.LOGGER.printInfo("********************** COLLECT REACHABLE SIGNATURES **********************");

        for(Sig sig : translator.alloyModel.getAllSigs())
        {
            if(sig.isTopLevel())
            {
                translator.topLevelSigs.add(sig);
            }
            translator.reachableSigs.add(sig);
        }
    }

    private void translateSignatures()
    {
        translator.reachableSigs.forEach((sig) ->
        {
            FunctionDeclaration functionDeclaration =  declareUnaryAtomFunction(Utils.sanitizeName(sig.toString()));
            translator.signaturesMap.put(sig, functionDeclaration);

            // if sig extends another signature
            if(! sig.isTopLevel())
            {
                translateSigSubsetParent(sig, functionDeclaration);
            }

            if (sig.isOne != null)
            {
                translateSignatureOneMultiplicity(sig);
            }

            if (sig.isLone != null)
            {
                translateSignatureLoneMultiplicity(sig);
            }

            if (sig.isSome != null)
            {
                translateSignatureSomeMultiplicity(sig);
            }

            // translateExpr signature fields
            for(Sig.Field field : sig.getFields())
            {
                this.fieldTranslator.translate(field);
            }
        });
    }

    private void translateSignatureOneMultiplicity(Sig sig)
    {
        FunctionDeclaration signature = translator.signaturesMap.get(sig);

        FunctionDeclaration declaration = generateAuxiliarySetNAtoms(signature);

        BinaryExpression subset   = new BinaryExpression(signature.getConstantExpr(), BinaryExpression.Op.EQ, declaration.getConstantExpr());
        translator.smtProgram.addAssertion(new Assertion(subset));
    }

    private void translateSignatureLoneMultiplicity(Sig sig)
    {
        FunctionDeclaration signature = translator.signaturesMap.get(sig);

        FunctionDeclaration declaration = generateAuxiliarySetNAtoms(signature);

        BinaryExpression subset   = new BinaryExpression(signature.getConstantExpr(), BinaryExpression.Op.SUBSET, declaration.getConstantExpr());
        translator.smtProgram.addAssertion(new Assertion(subset));
    }

    private void translateSignatureSomeMultiplicity(Sig sig)
    {
        FunctionDeclaration signature = translator.signaturesMap.get(sig);

        FunctionDeclaration declaration = generateAuxiliarySetNAtoms(signature);

        BinaryExpression subset   = new BinaryExpression(declaration.getConstantExpr(), BinaryExpression.Op.SUBSET, signature.getConstantExpr());
        translator.smtProgram.addAssertion(new Assertion(subset));
    }

    private FunctionDeclaration generateAuxiliarySetNAtoms(FunctionDeclaration signature)
    {
        List<Expression> expressions = declareNDistinctConstants(translator.atomSort, 1);

        FunctionDeclaration declaration = new FunctionDeclaration(Utils.getNewSet(), signature.getOutputSort());

        translator.smtProgram.addFunctionDeclaration(declaration);

        Expression set = new UnaryExpression(UnaryExpression.Op.SINGLETON, expressions.get(expressions.size() - 1));

        if(expressions.size() > 1)
        {
            List<Expression> atoms = Arrays.asList(set);

            for(int i = expressions.size() - 2; i >= 0; i--)
            {
                atoms.add(expressions.get(i));
            }

            set = new MultiArityExpression(MultiArityExpression.Op.INSERT, atoms);
        }

        BinaryExpression equality = new BinaryExpression(declaration.getConstantExpr(), BinaryExpression.Op.EQ, set);

        translator.smtProgram.addAssertion(new Assertion(equality));
        return declaration;
    }

    private List<Expression> declareNDistinctConstants(Sort sort,int n)
    {
        List<Expression> expressions = new ArrayList<>();
        if(n > 0)
        {
            for (int i = 0; i < n; i++)
            {
                ConstantDeclaration constantDeclaration = new ConstantDeclaration(Utils.getNewAtom(), sort);
                MultiArityExpression makeTuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, constantDeclaration.getConstantExpr());
                expressions.add(makeTuple);
                translator.smtProgram.addConstantDeclaration(constantDeclaration);
            }

            if (n > 1)
            {
                MultiArityExpression distinct = new MultiArityExpression(MultiArityExpression.Op.DISTINCT, expressions);
                translator.smtProgram.addAssertion(new Assertion(distinct));
            }
        }
        else
        {
            translator.LOGGER.printSevere("Argument n should be greater than 0");
        }
        return expressions;
    }

    private void translateSigSubsetParent(Sig sig, FunctionDeclaration functionDeclaration)
    {
        if(sig instanceof Sig.PrimSig)
        {
            Sig                 parent              = ((Sig.PrimSig) sig).parent;
            FunctionDeclaration parentDeclaration   = translator.signaturesMap.get(parent);
            BinaryExpression    subsetExpression    = new BinaryExpression(functionDeclaration.getConstantExpr(), BinaryExpression.Op.SUBSET, parentDeclaration.getConstantExpr());
            translator.smtProgram.addAssertion(new Assertion(subsetExpression));
        }
        else
        {
            List<Sig> parents             = ((Sig.SubsetSig) sig).parents;
            if(parents.size() == 1)
            {
                FunctionDeclaration parentDeclaration   = translator.signaturesMap.get(parents.get(0));
                BinaryExpression    subset              = new BinaryExpression(functionDeclaration.getConstantExpr(), BinaryExpression.Op.SUBSET, parentDeclaration.getConstantExpr());
                translator.smtProgram.addAssertion(new Assertion(subset));
            }
            else
            {
                Expression          left    = translator.signaturesMap.get(parents.get(0)).getConstantExpr();
                Expression          right   = translator.signaturesMap.get(parents.get(1)).getConstantExpr();
                BinaryExpression    union   = new BinaryExpression(left, BinaryExpression.Op.UNION, right);

                for (int i = 2; i < parents.size(); i++)
                {
                    Expression expression   = translator.signaturesMap.get(parents.get(i)).getConstantExpr();
                    union                   = new BinaryExpression(union, BinaryExpression.Op.UNION, expression);
                }

                BinaryExpression subset     = new BinaryExpression(functionDeclaration.getConstantExpr(), BinaryExpression.Op.SUBSET, union);
                translator.smtProgram.addAssertion(new Assertion(subset));
            }
        }
    }


    private FunctionDeclaration declareUnaryAtomFunction(String varName)
    {
        FunctionDeclaration declaration = null;
        if(varName != null)
        {
            declaration = new FunctionDeclaration(varName, translator.setOfUnaryAtomSort);
            translator.smtProgram.addFunctionDeclaration(declaration);
        }
        return declaration;
    }

    public void translate()
    {
        collectReachableSigs();
        translateSignatures();
        translateSignatureHierarchies();
    }
}
