/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt;

import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompModule;
import edu.uiowa.alloy2smt.smtAst.*;

import java.util.*;
import java.util.stream.Collectors;

public class Alloy2SMTTranslator
{
    public final SMTProgram smtProgram;
    
    private final Alloy2SMTLogger   LOGGER = new Alloy2SMTLogger("Alloy2SMTTranslator");
    
    private final String                    atom;
    private final CompModule                alloyModel;
    private final List<Sig>                 reachableSigs;
    private final List<Sig>                 topLevelSigs;
    private final SetSort                   setOfUnaryAtomSort;
    private final SetSort                   setOfBinaryAtomSort;
    private final UninterpretedSort         atomSort;
    private final TupleSort                 unaryAtomSort;
    private final TupleSort                 binaryAtomSort;

    private Map<Sig,VariableDeclaration>    signaturesMap = new HashMap<>();

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
    }

    public SMTProgram execute()
    {        
        collectReachableSigs();
        translateSigsAndHierarchy();
        return new SMTProgram();
    }
    
    private void collectReachableSigs() 
    {
        LOGGER.printInfo("********************** COLLECT REACHABLE SIGNATURES **********************");
        
        for(Sig sig : this.alloyModel.getAllSigs()) 
        {
            if(sig.isTopLevel()) 
            {
                this.topLevelSigs.add(sig);
            }
            this.reachableSigs.add(sig);
        }
    } 
    
    private void translateSigsAndHierarchy() 
    {
        this.reachableSigs.forEach((sig) -> {

            VariableDeclaration variableDeclaration =  mkAndAddUnaryAtomRelation(Utils.sanitizeName(sig.toString()));
            this.signaturesMap.put(sig, variableDeclaration);
            // translate signature fields
            for(Sig.Field field : sig.getFields())
            {
                translateField(field);
            }
        });
    }

    private void translateField(Sig.Field field)
    {

        String              fieldName   = Utils.sanitizeName(field.sig.label + "/" + field.label);
        TupleSort           tupleSort   = new TupleSort(Collections.nCopies(field.type().arity(), this.atomSort));
        SetSort             setSort     = new SetSort(tupleSort);
        VariableDeclaration declaration = new VariableDeclaration(fieldName, tupleSort);

        // declare a variable for the field
        this.smtProgram.addVarDecl(declaration);

        // a field relation is a subset of the product of its signatures
        List<Sig>           fieldSignatures     =  field.type().fold().stream().flatMap(List::stream).collect(Collectors.toList());

        /* alloy: sig Book{addr: Name -> lone Addr}
        *  smt  : (assert (subset addr (product (product Book Name) Addr)))
        */
        VariableExpression  first   = new VariableExpression(signaturesMap.get(fieldSignatures.get(0)).getVarName());
        VariableExpression  second  = new VariableExpression(signaturesMap.get(fieldSignatures.get(1)).getVarName());
        BinaryExpression    product = new BinaryExpression(first, BinaryExpression.Op.PRODUCT, second);

        for(int i = 2; i < fieldSignatures.size(); i++)
        {
            VariableExpression  expr = new VariableExpression(signaturesMap.get(fieldSignatures.get(i)).getVarName());
            product                  = new BinaryExpression(product, BinaryExpression.Op.PRODUCT, expr);
        }

        VariableExpression  fieldExpr   = new VariableExpression(declaration.getVarName());
        BinaryExpression    subset      = new BinaryExpression(fieldExpr, BinaryExpression.Op.SUBSET, product);
        Assertion           assertion   = new Assertion(subset);

        this.smtProgram.addAssertion(assertion);
    }

    private VariableDeclaration mkAndAddUnaryAtomRelation(String varName)
    {
        VariableDeclaration variable = null;
        if(varName != null)
        {
            variable = new VariableDeclaration(varName, this.setOfUnaryAtomSort);
            this.smtProgram.addVarDecl(variable);
        }
        return variable;
    }
    
    private void mkAndAddBinaryAtomRelation(String varName) 
    {
        if(varName != null) 
        {
            this.smtProgram.addVarDecl(new VariableDeclaration(varName, this.setOfBinaryAtomSort));
        }        
    }    
    
    private void addToVarDecl(VariableDeclaration varDecl) 
    {
        if(varDecl != null) 
        {
            this.smtProgram.addVarDecl(varDecl);
        }
        else 
        {
            LOGGER.printSevere("Try to add a null variable declaration!");
        }
    }
    
    private void addToFcnDecl(FunctionDeclaration fcnDecl) 
    {
        if(fcnDecl != null) 
        {
            this.smtProgram.addFcnDecl(fcnDecl);
        }
        else 
        {
            LOGGER.printSevere("Try to add a null function declaration!");
        }
    }    
    
    private void addToFcnDef(FunctionDefinition fcnDef) 
    {
        if(fcnDef != null) 
        {
            this.smtProgram.addFcnDef(fcnDef);
        }
        else 
        {
            LOGGER.printSevere("Try to add a null function declaration!");
        }
    }    
}
