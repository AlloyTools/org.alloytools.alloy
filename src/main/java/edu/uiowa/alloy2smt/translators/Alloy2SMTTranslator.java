/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.parser.CompModule;
import edu.uiowa.alloy2smt.Alloy2SMTLogger;
import edu.uiowa.alloy2smt.smtAst.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class Alloy2SMTTranslator
{
    public final SMTProgram smtProgram;
    
    final Alloy2SMTLogger LOGGER = new Alloy2SMTLogger("Alloy2SMTTranslator");
    
    final String                    atom;
    final CompModule                alloyModel;
    final List<Sig>                 reachableSigs;
    final List<Sig>                 topLevelSigs;
    final SetSort                   setOfUnaryAtomSort;
    final SetSort                   setOfBinaryAtomSort;
    final UninterpretedSort         atomSort;
    final TupleSort                 unaryAtomSort;
    final TupleSort                 binaryAtomSort;
    final SignatureTranslator       signatureTranslator;
    final ExprTranslator            exprTranslator;

    Map<Sig,FunctionDeclaration>        signaturesMap   = new HashMap<>();
    Map<Sig.Field,FunctionDeclaration>  fieldsMap       = new HashMap<>();


    public Alloy2SMTTranslator(CompModule alloyModel)
    {
        this.smtProgram             = new SMTProgram();
        
        this.atom                   = "Atom";
        this.alloyModel             = alloyModel;
        this.reachableSigs          = new ArrayList<>();
        this.topLevelSigs           = new ArrayList<>();
        this.atomSort               = new UninterpretedSort(this.atom);
        this.unaryAtomSort          = new TupleSort(this.atomSort);
        this.binaryAtomSort         = new TupleSort(this.atomSort, this.atomSort);
        this.setOfUnaryAtomSort     = new SetSort(this.unaryAtomSort);
        this.setOfBinaryAtomSort    = new SetSort(this.binaryAtomSort);
        this.signatureTranslator    = new SignatureTranslator(this);
        this.exprTranslator         = new ExprTranslator(this);
    }

    public SMTProgram execute()
    {        

        this.signatureTranslator.translate();
        translateFacts();
        return this.smtProgram;
    }

    private void translateFacts()
    {
        for (Pair<String, Expr> pair :this.alloyModel.getAllFacts() )
        {
            translateFact(pair.a, pair.b);
        }
    }

    private void translateFact(String factName, Expr factExpr)
    {
        Map<String, ConstantExpression> variablesScope = new HashMap<>();
        Expression expression = this.exprTranslator.translateExpr(factExpr, variablesScope);
        this.smtProgram.addAssertion(new Assertion(factName, expression));
    }
}
