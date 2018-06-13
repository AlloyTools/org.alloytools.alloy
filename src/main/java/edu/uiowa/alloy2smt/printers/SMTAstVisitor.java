/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.printers;

import edu.uiowa.alloy2smt.smtAst.BinaryExpression;
import edu.uiowa.alloy2smt.smtAst.FunctionDeclaration;
import edu.uiowa.alloy2smt.smtAst.FunctionDefinition;
import edu.uiowa.alloy2smt.smtAst.IntConstant;
import edu.uiowa.alloy2smt.smtAst.IntSort;
import edu.uiowa.alloy2smt.smtAst.QuantifiedExpression;
import edu.uiowa.alloy2smt.smtAst.RealSort;
import edu.uiowa.alloy2smt.smtAst.SetSort;
import edu.uiowa.alloy2smt.smtAst.StringSort;
import edu.uiowa.alloy2smt.smtAst.TupleSort;
import edu.uiowa.alloy2smt.smtAst.UnaryExpression;
import edu.uiowa.alloy2smt.smtAst.UninterpretedSort;
import edu.uiowa.alloy2smt.smtAst.VariableDeclaration;
import edu.uiowa.alloy2smt.smtAst.VariableExpression;

public interface SMTAstVisitor 
{
    public void visit(BinaryExpression bExpr);    
    
    public void visit(IntSort intSort);   

    public void visit(QuantifiedExpression aThis);

    public void visit(RealSort aThis);

    public void visit(SetSort aThis);

    public void visit(StringSort aThis);

    public void visit(TupleSort aThis);

    public void visit(UnaryExpression aThis);

    public void visit(UninterpretedSort aThis);

    public void visit(IntConstant aThis);

    public void visit(VariableExpression aThis);

    public void visit(FunctionDeclaration aThis);

    public void visit(FunctionDefinition aThis);

    public void visit(VariableDeclaration aThis);
}
