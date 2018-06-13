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
import edu.uiowa.alloy2smt.smtAst.FunctionDeclaration;
import edu.uiowa.alloy2smt.smtAst.FunctionDefinition;
import edu.uiowa.alloy2smt.smtAst.SMTProgram;
import edu.uiowa.alloy2smt.smtAst.SetSort;
import edu.uiowa.alloy2smt.smtAst.TupleSort;
import edu.uiowa.alloy2smt.smtAst.UninterpretedSort;
import edu.uiowa.alloy2smt.smtAst.VariableDeclaration;
import java.util.ArrayList;
import java.util.List;

public class Alloy2SMTTranslator
{
    public final SMTProgram smtProgram;
    
    private final Alloy2SMTLogger   LOGGER = new Alloy2SMTLogger("Alloy2SMTTranslator");
    
    private final String                atom;
    private final CompModule            alloyModel;
    private final List<Sig>             reachableSigs;
    private final List<Sig>             topLevelSigs;
    private final SetSort               unarySetOfAtomSort;
    private final SetSort               binarySetOfAtomSort;
    private final UninterpretedSort     atomSort;
    private final TupleSort             unaryAtomSort;
    private final TupleSort             binaryAtomSort;

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
        this.unarySetOfAtomSort     = new SetSort(this.unaryAtomSort);
        this.binarySetOfAtomSort    = new SetSort(this.binaryAtomSort);
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
            mkAndAddUnaryAtomRelation(Utils.sanitizeName(sig.toString()));
        });
    } 
    
    private void mkAndAddUnaryAtomRelation(String varName) 
    {
        if(varName != null) 
        {
            this.smtProgram.addVarDecl(new VariableDeclaration(varName, this.unarySetOfAtomSort));
        }        
    }
    
    private void mkAndAddBinaryAtomRelation(String varName) 
    {
        if(varName != null) 
        {
            this.smtProgram.addVarDecl(new VariableDeclaration(varName, this.binarySetOfAtomSort));
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
