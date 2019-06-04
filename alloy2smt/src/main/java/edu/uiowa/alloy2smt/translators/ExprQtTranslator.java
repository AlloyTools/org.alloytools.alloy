package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;

import java.util.*;
import java.util.stream.Collectors;

public class ExprQtTranslator
{
    final ExprTranslator exprTranslator;
    final ExprUnaryTranslator exprUnaryTranslator;
    final ExprBinaryTranslator exprBinaryTranslator;
    final Alloy2SmtTranslator translator;

    public ExprQtTranslator(ExprTranslator exprTranslator)
    {
        this.exprTranslator = exprTranslator;
        this.exprUnaryTranslator = exprTranslator.exprUnaryTranslator;
        this.exprBinaryTranslator = exprTranslator.exprBinaryTranslator;
        this.translator = exprTranslator.translator;
    }

    Expression translateExprQt(ExprQt exprQt, Map<String, Expression> variablesScope)
    {
        Map<String, List<VariableDeclaration>> quantifiedSingleton2AtomMap = new HashMap<>();
        Map<String, Expression> quantifiedVariable2ExpressionMap = new HashMap<>();
        LinkedHashMap<String, Expression> quantifiedVariable2SignatureMap = new LinkedHashMap<>();

        Expression multiplicityConstraint = new BoolConstant(true);

        for (Decl decl: exprQt.decls)
        {
            Expression declExpr     = exprTranslator.translateExpr(decl.expr, variablesScope);
            List<Sort> declSorts    = AlloyUtils.getExprSorts(decl.expr);

            //cases a: [one, some, set, lone] A where A has arity 1
            if( decl.expr instanceof ExprUnary && decl.expr.type().hasArity(1))
            {
                Sort sort = declSorts.get(0).getSort();
                declSorts = declSorts.stream()
                                     .map(s -> new SetSort(new TupleSort(s)))
                                     .collect(Collectors.toList());
                for(ExprHasName name : decl.names)
                {
                    String sanitizedName = TranslatorUtils.sanitizeName(name.label);
                    VariableDeclaration variable = createVariable(declSorts.get(0), sanitizedName);
                    //ToDo: refactor this for set case
                    quantifiedSingleton2AtomMap.put(name.label, new ArrayList<>(Collections.singletonList(variable)));
                    variablesScope.put(name.label, variable.getVariable());
                    quantifiedVariable2SignatureMap.put(name.label, declExpr);
                    quantifiedVariable2ExpressionMap.put(name.label, variable.getVariable());

                    switch (((ExprUnary) decl.expr).op)
                    {
                        case SOMEOF:
                        {
                            multiplicityConstraint = new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(variable.getVariable(), BinaryExpression.Op.EQ,
                                    new UnaryExpression(UnaryExpression.Op.EMPTYSET, variable.getSort())
                            ));
                        } break;
                        case NOOP: // NOOP is the same as ONEOF in case of
                        case ONEOF:
                        {
                            VariableDeclaration multiplicityVariable = createVariable(sort, TranslatorUtils.getNewName());
                            quantifiedSingleton2AtomMap.get(name.label).add(multiplicityVariable);
                            multiplicityConstraint = new BinaryExpression(variable.getVariable(), BinaryExpression.Op.EQ,
                                    new UnaryExpression(UnaryExpression.Op.SINGLETON,
                                            new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, multiplicityVariable.getVariable()))
                            );
                        } break;
                        case LONEOF:
                        {
                            VariableDeclaration multiplicityVariable = createVariable(sort, TranslatorUtils.getNewName());

                            quantifiedSingleton2AtomMap.get(name.label).add(multiplicityVariable);
                            multiplicityConstraint = new BinaryExpression(variable.getVariable(), BinaryExpression.Op.SUBSET,
                                    new UnaryExpression(UnaryExpression.Op.SINGLETON,
                                            new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, multiplicityVariable.getVariable()))
                            );
                        } break;
                    }
                }
            }
            else
            {
                for (ExprHasName name : decl.names)
                {
                    Sort declExprSort = declSorts.get(0);
                    int arity = decl.expr.type().arity();
                    String sanBdVarName = TranslatorUtils.sanitizeName(name.label);

                    VariableDeclaration bdVarDecl = createVariable(declExprSort, sanBdVarName);
                    Expression bdVarTupleExpr = bdVarDecl.getVariable();
                    List<VariableDeclaration> bdAtomVars = new ArrayList<>();

                    if (arity > 1)
                    {
                        List<Expression> bdAtomExprs = new ArrayList<>();

                        for (int i = 0; i < arity; i++) {
                            Expression bdAtomVarExpr;
                            String varName = sanBdVarName + "_" + i;
                            VariableDeclaration bdAtomVar;

                            if (declSorts.get(i) instanceof IntSort) {
                                bdAtomVar = new VariableDeclaration(varName, AbstractTranslator.uninterpretedInt);
                                bdAtomVarExpr = exprBinaryTranslator.mkTupleSelectExpr(exprUnaryTranslator.mkUnaryIntTupValue(bdAtomVar.getVariable()), 0);
                            } else {
                                bdAtomVar = new VariableDeclaration(varName, AbstractTranslator.atomSort);
                                bdAtomVarExpr = bdAtomVar.getVariable();
                            }
                            bdAtomVars.add(bdAtomVar);
                            bdAtomExprs.add(bdAtomVarExpr);
                        }
                        bdVarTupleExpr = exprUnaryTranslator.mkOneTupleExprOutofAtoms(bdAtomExprs);
                        quantifiedVariable2ExpressionMap.put(sanBdVarName, bdVarTupleExpr);
                        quantifiedSingleton2AtomMap.put(sanBdVarName, bdAtomVars);
                    } else {
                        bdAtomVars.add(bdVarDecl);
                        if ((declExprSort instanceof IntSort)) {
                            bdVarTupleExpr = exprUnaryTranslator.mkUnaryIntTupValue(bdVarDecl.getVariable());
                        } else {
                            bdVarTupleExpr = exprUnaryTranslator.mkOneTupleExprOutofAtoms(bdVarTupleExpr);
                        }
                        quantifiedVariable2ExpressionMap.put(sanBdVarName, bdVarTupleExpr);
                        quantifiedSingleton2AtomMap.put(sanBdVarName, bdAtomVars);
                    }

                    variablesScope.put(name.label, AlloyUtils.mkSingletonOutOfTuple(bdVarTupleExpr));
                    quantifiedVariable2SignatureMap.put(sanBdVarName, declExpr);
                }
            }
        }

        // Translate quantified expression body
        Expression bodyExpr = exprTranslator.translateExpr(exprQt.sub, variablesScope);

        switch (exprQt.op)
        {
            case ALL    : return  translateAllQuantifier(quantifiedVariable2SignatureMap, quantifiedSingleton2AtomMap, quantifiedVariable2ExpressionMap, bodyExpr, multiplicityConstraint);
            case SOME   : return  translateSomeQuantifier(quantifiedVariable2SignatureMap, quantifiedSingleton2AtomMap, quantifiedVariable2ExpressionMap, bodyExpr, multiplicityConstraint);
            case NO     : return  translateNoQuantifier(quantifiedVariable2SignatureMap, quantifiedSingleton2AtomMap, quantifiedVariable2ExpressionMap, bodyExpr, multiplicityConstraint);
            case LONE   : {
                Map<String, List<VariableDeclaration>>         sndBdVarNameTobdAtomVars    = new HashMap<>();
                Map<String, Expression>                             sndBdVarNameToTupleExpr     = new HashMap<>();
                LinkedHashMap<String, Expression>                   sndBdVarNameToExprMap       = new LinkedHashMap<>();

                Expression sndBodyExpr = createSndSetBdvarsAndExpr(sndBdVarNameToExprMap, sndBdVarNameTobdAtomVars, sndBdVarNameToTupleExpr, variablesScope, exprQt);

                return  translateLoneQuantifier(quantifiedVariable2SignatureMap, sndBdVarNameToExprMap, quantifiedSingleton2AtomMap, sndBdVarNameTobdAtomVars,
                        quantifiedVariable2ExpressionMap, sndBdVarNameToTupleExpr, bodyExpr, sndBodyExpr, multiplicityConstraint);
            }
            case ONE    : {
                Map<String, List<VariableDeclaration>>         sndBdVarNameTobdAtomVars    = new HashMap<>();
                Map<String, Expression>                             sndBdVarNameToTupleExpr     = new HashMap<>();
                LinkedHashMap<String, Expression>                   sndBdVarNameToExprMap       = new LinkedHashMap<>();

                Expression sndBodyExpr = createSndSetBdvarsAndExpr(sndBdVarNameToExprMap, sndBdVarNameTobdAtomVars, sndBdVarNameToTupleExpr, variablesScope, exprQt);

                return  translateOneQuantifier(quantifiedVariable2SignatureMap, sndBdVarNameToExprMap, quantifiedSingleton2AtomMap, sndBdVarNameTobdAtomVars,
                        quantifiedVariable2ExpressionMap, sndBdVarNameToTupleExpr, bodyExpr, sndBodyExpr, multiplicityConstraint);
            }
            case COMPREHENSION :
            {
                List<Sort> elementSorts     = new ArrayList<>();

                for(int i = 0; i < exprQt.decls.size(); ++i)
                {
                    for(int j = 0; j < exprQt.decls.get(i).names.size(); ++j)
                    {
                        elementSorts.addAll(AlloyUtils.getExprSorts(exprQt.decls.get(i).expr));
                    }
                }

                String              setBdVarName    = TranslatorUtils.getNewSetName();
                SetSort             setSort         = new SetSort(new TupleSort(elementSorts));
                VariableDeclaration setBdVar   = new VariableDeclaration(setBdVarName, setSort);
                LinkedHashMap<VariableDeclaration, Expression> bdVars = new LinkedHashMap<>();

                for(Decl decl : exprQt.decls)
                {
                    Expression declExpr         = exprTranslator.translateExpr(decl.expr, variablesScope);
                    List<Sort> declExprSorts    = AlloyUtils.getExprSorts(decl.expr);

                    for (ExprHasName name: decl.names)
                    {
                        String sanitizedName = TranslatorUtils.sanitizeName(name.label);
                        VariableDeclaration bdVar = new VariableDeclaration(sanitizedName, declExprSorts.get(0));
                        variablesScope.put(name.label, bdVar.getVariable());
                        bdVars.put(bdVar, declExpr);
                    }
                }
                Expression setCompBodyExpr  = exprTranslator.translateExpr(exprQt.sub, variablesScope);
                Expression membership       = AlloyUtils.getMemberExpression(bdVars, 0);

                for(int i = 1; i < bdVars.size(); ++i)
                {
                    membership = new BinaryExpression(membership, BinaryExpression.Op.AND, AlloyUtils.getMemberExpression(bdVars, i));
                }
                membership = new BinaryExpression(membership, BinaryExpression.Op.AND, setCompBodyExpr);
                Expression setMembership = new BinaryExpression(exprUnaryTranslator.mkTupleExpr(new ArrayList<>(bdVars.keySet())), BinaryExpression.Op.MEMBER, setBdVar.getVariable());
                membership = new BinaryExpression(membership, BinaryExpression.Op.EQ, setMembership);
                Expression forallExpr = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new ArrayList<>(bdVars.keySet()), membership);

                if(translator.auxExpr != null)
                {
                    translator.auxExpr = new BinaryExpression(translator.auxExpr, BinaryExpression.Op.AND, forallExpr);
                }
                else
                {
                    translator.auxExpr = forallExpr;
                }

                translator.existentialBdVars.add(setBdVar);
                return setBdVar.getVariable();
            }
            default: throw new UnsupportedOperationException();
        }
    }

    //ToDo: review removing this function
    VariableDeclaration createVariable(Sort sort, String name)
    {
        if(sort instanceof IntSort)
        {
            return new VariableDeclaration(name, Alloy2SmtTranslator.uninterpretedInt);
        }
        return new VariableDeclaration(name, sort);
    }

    private Expression createSndSetBdvarsAndExpr(LinkedHashMap<String, Expression> bdVarToExprMap,
                                                 Map<String, List<VariableDeclaration>> bdTupVarNameTobdAtomVars,
                                                 Map<String, Expression> bdTupVarNameToTupleExpr,
                                                 Map<String, Expression> variablesScope, ExprQt exprQt)
    {
        for (Decl decl: exprQt.decls)
        {
            Expression declExpr     = exprTranslator.translateExpr(decl.expr, variablesScope);
            List<Sort> declSorts    = AlloyUtils.getExprSorts(decl.expr);

            for (ExprHasName name: decl.names)
            {
                Sort    declExprSort    = declSorts.get(0);
                int     arity           = decl.expr.type().arity();
                String  sanBdVarName    = TranslatorUtils.sanitizeName(name.label);

                VariableDeclaration bdVarDecl = createVariable(declExprSort, sanBdVarName);
                Expression bdVarTupleExpr = bdVarDecl.getVariable();
                List<VariableDeclaration>  bdAtomVars    = new ArrayList<>();

                if(arity > 1)
                {
                    List<Expression> bdAtomExprs   = new ArrayList<>();
                    for(int i = 0; i < arity; i++)
                    {
                        Expression bdAtomVarExpr;
                        String varName = sanBdVarName+"_"+i+"_2";
                        VariableDeclaration bdAtomVar;

                        if(declSorts.get(i) instanceof IntSort)
                        {
                            bdAtomVar = new VariableDeclaration(varName, translator.uninterpretedInt);
                            bdAtomVarExpr = exprBinaryTranslator.mkTupleSelectExpr(exprUnaryTranslator.mkUnaryIntTupValue(bdAtomVar.getVariable()), 0);
                        }
                        else
                        {
                            bdAtomVar = new VariableDeclaration(varName, translator.atomSort);
                            bdAtomVarExpr = bdAtomVar.getVariable();
                        }
                        bdAtomVars.add(bdAtomVar);
                        bdAtomExprs.add(bdAtomVarExpr);
                    }
                    bdVarTupleExpr = exprUnaryTranslator.mkOneTupleExprOutofAtoms(bdAtomExprs);
                    bdTupVarNameToTupleExpr.put(sanBdVarName, bdVarTupleExpr);
                    bdTupVarNameTobdAtomVars.put(sanBdVarName, bdAtomVars);
                }
                else
                {
                    bdAtomVars.add(bdVarDecl);
                    if((declExprSort instanceof IntSort))
                    {
                        bdVarTupleExpr = exprUnaryTranslator.mkUnaryIntTupValue(bdVarDecl.getVariable());
                    }
                    else
                    {
                        bdVarTupleExpr = exprUnaryTranslator.mkOneTupleExprOutofAtoms(bdVarTupleExpr);
                    }
                    bdTupVarNameToTupleExpr.put(sanBdVarName, bdVarTupleExpr);
                    bdTupVarNameTobdAtomVars.put(sanBdVarName, bdAtomVars);
                }
                variablesScope.put(name.label, AlloyUtils.mkSingletonOutOfTuple(bdVarTupleExpr));
                bdVarToExprMap.put(sanBdVarName, declExpr);
            }
        }

        // Translate quantified expression body
        return exprTranslator.translateExpr(exprQt.sub, variablesScope);
    }


    // (all e: R|not P) or (some e : R | P and all e2 : R | not(e = e2) => not P)
    private Expression translateLoneQuantifier(LinkedHashMap<String, Expression> quantifiedVariable2SignatureMap, LinkedHashMap<String, Expression> sndBdVarToExprMap,
                                               Map<String, List<VariableDeclaration>> bdVarNameTobdAtomVars, Map<String, List<VariableDeclaration>> sndBdVarNameTobdAtomVars,
                                               Map<String, Expression> bdVarNameToTupleExpr, Map<String, Expression> sndBdVarNameToTupleExpr,
                                               Expression bodyExpr, Expression sndBodyExpr, Expression multiplicityConstraint)
    {
        Expression fstPartBodyExpr = bodyExpr;
        Expression sndPartBodyExpr = bodyExpr;
        Expression thdPartBodyExpr = sndBodyExpr;

        // (all e: R|not P)
        List<VariableDeclaration> fstBdVars = new ArrayList<>();
        for(List<VariableDeclaration> bdVars : bdVarNameTobdAtomVars.values())
        {
            fstBdVars.addAll(bdVars);
        }
        Expression fstMembership = getSubsetConstraints(quantifiedVariable2SignatureMap, bdVarNameToTupleExpr, multiplicityConstraint);
        Expression fstBodyExpr = new BinaryExpression(fstMembership, BinaryExpression.Op.IMPLIES, new UnaryExpression(UnaryExpression.Op.NOT, bodyExpr));
        QuantifiedExpression fstQuantExpr = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, fstBdVars, fstBodyExpr);

        // some e1 : R | P
        Expression sndExistExpr = new BinaryExpression(fstMembership, BinaryExpression.Op.AND, sndPartBodyExpr);

        // Membership constraints of the universal constraints all e2 : R | not(e1 = e2) => not P)
        // all e2 : R

        List<VariableDeclaration> sndBdVars = new ArrayList<>();
        for(List<VariableDeclaration> bdVars : sndBdVarNameTobdAtomVars.values())
        {
            sndBdVars.addAll(bdVars);
        }

        // all e2 : R | not(e1 = e2) => not P
        Expression distExpr = getSubsetConstraints(sndBdVarToExprMap, sndBdVarNameToTupleExpr, multiplicityConstraint);

        for(Map.Entry<String, Expression> varNameToExpr : bdVarNameToTupleExpr.entrySet())
        {
            Expression fstExpr = varNameToExpr.getValue();
            Expression sndExpr = sndBdVarNameToTupleExpr.get(varNameToExpr.getKey());
            distExpr = new BinaryExpression(distExpr, BinaryExpression.Op.AND, new MultiArityExpression(MultiArityExpression.Op.DISTINCT, fstExpr, sndExpr));
        }
        distExpr = new BinaryExpression(distExpr, BinaryExpression.Op.IMPLIES, new UnaryExpression(UnaryExpression.Op.NOT, thdPartBodyExpr));
        QuantifiedExpression sndForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, sndBdVars, distExpr);
        // (some e : R | P and all e2 : R | not(e = e2) => not P)
        QuantifiedExpression existFormula = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, fstBdVars, new BinaryExpression(sndExistExpr, BinaryExpression.Op.AND, sndForall));

        return new BinaryExpression(fstQuantExpr, BinaryExpression.Op.OR, existFormula);
    }

    // (some e : R | P and all e2 : R | not(e = e2) => not P)
    private Expression translateOneQuantifier(LinkedHashMap<String, Expression> quantifiedVariable2SignatureMap, LinkedHashMap<String, Expression> sndBdVarToExprMap,
                                              Map<String, List<VariableDeclaration>> bdVarNameTobdAtomVars, Map<String, List<VariableDeclaration>> sndBdVarNameTobdAtomVars,
                                              Map<String, Expression> bdVarNameToTupleExpr, Map<String, Expression> sndBdVarNameToTupleExpr,
                                              Expression bodyExpr, Expression sndBodyExpr,
                                              Expression multiplicityConstraint)
    {
        Expression fstPartBodyExpr = bodyExpr;
        Expression sndPartBodyExpr = bodyExpr;
        Expression thdPartBodyExpr = sndBodyExpr;

        // (all e: R|not P)
        List<VariableDeclaration> fstBdVars = new ArrayList<>();

        for(List<VariableDeclaration> bdVars : bdVarNameTobdAtomVars.values())
        {
            fstBdVars.addAll(bdVars);
        }
        Expression fstMembership = getSubsetConstraints(quantifiedVariable2SignatureMap, bdVarNameToTupleExpr, multiplicityConstraint);

        // some e1 : R | P
        Expression sndExistExpr = new BinaryExpression(fstMembership, BinaryExpression.Op.AND, sndPartBodyExpr);

        // Membership constraints of the universal constraints all e2 : R | not(e1 = e2) => not P)
        // all e2 : R

        List<VariableDeclaration> sndBdVars = new ArrayList<>();
        for(List<VariableDeclaration> bdVars : sndBdVarNameTobdAtomVars.values())
        {
            sndBdVars.addAll(bdVars);
        }

        // all e2 : R | not(e1 = e2) => not P
        Expression distExpr = getSubsetConstraints(sndBdVarToExprMap, sndBdVarNameToTupleExpr, multiplicityConstraint);

        for(Map.Entry<String, Expression> varNameToExpr : bdVarNameToTupleExpr.entrySet())
        {
            Expression fstExpr = varNameToExpr.getValue();
            Expression sndExpr = sndBdVarNameToTupleExpr.get(varNameToExpr.getKey());
            distExpr = new BinaryExpression(distExpr, BinaryExpression.Op.AND, new MultiArityExpression(MultiArityExpression.Op.DISTINCT, fstExpr, sndExpr));
        }
        distExpr = new BinaryExpression(distExpr, BinaryExpression.Op.IMPLIES, new UnaryExpression(UnaryExpression.Op.NOT, thdPartBodyExpr));
        QuantifiedExpression sndForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, sndBdVars, distExpr);
        // (some e : R | P and all e2 : R | not(e = e2) => not P)
        QuantifiedExpression existFormula = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, fstBdVars, new BinaryExpression(sndExistExpr, BinaryExpression.Op.AND, sndForall));

        return existFormula;
    }

    private QuantifiedExpression translateNoQuantifier(LinkedHashMap<String, Expression> quantifiedVariable2SignatureMap, Map<String, List<VariableDeclaration>> bdTupVarNameTobdAtomVars, Map<String, Expression> bdTupVarNameToTupleExpr, Expression bodyExpr,
                                                       Expression multiplicityConstraint)
    {
        List<VariableDeclaration> bdVars = new ArrayList<>();
        Expression membership = getSubsetConstraints(quantifiedVariable2SignatureMap, bdTupVarNameToTupleExpr, multiplicityConstraint);
        bodyExpr = new BinaryExpression(membership, BinaryExpression.Op.IMPLIES, new UnaryExpression(UnaryExpression.Op.NOT, bodyExpr));
        for(List<VariableDeclaration> vars : bdTupVarNameTobdAtomVars.values())
        {
            bdVars.addAll(vars);
        }
        QuantifiedExpression quantifiedExpression = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, bdVars, bodyExpr);
        return quantifiedExpression;
    }

    private QuantifiedExpression translateAllQuantifier(LinkedHashMap<String, Expression> quantifiedVariable2SignatureMap, Map<String, List<VariableDeclaration>> bdTupVarNameTobdAtomVars, Map<String, Expression> bdTupVarNameToTupleExpr, Expression bodyExpr,
                                                        Expression multiplicityConstraint)
    {
        List<VariableDeclaration> bdVars = new ArrayList<>();
        Expression membership = getSubsetConstraints(quantifiedVariable2SignatureMap, bdTupVarNameToTupleExpr, multiplicityConstraint);
        bodyExpr = new BinaryExpression(membership, BinaryExpression.Op.IMPLIES, bodyExpr);
        for(List<VariableDeclaration> vars : bdTupVarNameTobdAtomVars.values())
        {
            bdVars.addAll(vars);
        }
        QuantifiedExpression quantifiedExpression = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, bdVars, bodyExpr);
        return quantifiedExpression;
    }

    private QuantifiedExpression translateSomeQuantifier(LinkedHashMap<String, Expression> quantifiedVariable2SignatureMap, Map<String, List<VariableDeclaration>> quantifiedSingleton2AtomMap, Map<String, Expression> quantifiedVariable2ExpressionMap, Expression bodyExpr, Expression multiplicityConstraint)
    {
        List<VariableDeclaration> bdVars = new ArrayList<>();
        Expression membership = getSubsetConstraints(quantifiedVariable2SignatureMap, quantifiedVariable2ExpressionMap, multiplicityConstraint);
        bodyExpr = new BinaryExpression(membership, BinaryExpression.Op.AND, bodyExpr);
        for(List<VariableDeclaration> vars : quantifiedSingleton2AtomMap.values())
        {
            bdVars.addAll(vars);
        }
        QuantifiedExpression quantifiedExpression = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, bdVars, bodyExpr);
        return quantifiedExpression;
    }

    private Expression getSubsetConstraints(LinkedHashMap<String, Expression> quantifiedVariable2SignatureMap, Map<String, Expression> quantifiedVariable2ExpressionMap, Expression multiplicityConstraint)
    {
        Expression constraint = new BoolConstant(true);

        for(Map.Entry<String, Expression> entry : quantifiedVariable2SignatureMap.entrySet())
        {
            String      name            = entry.getKey();
            Expression  setExpression   = entry.getValue();
            Expression  quantifiedVariableExpression   = quantifiedVariable2ExpressionMap.get(name);

            // add constraint (member (mkTuple x) A) for x: A
            if(quantifiedVariableExpression.getSort() instanceof TupleSort)
            {
                constraint = new BinaryExpression(constraint, BinaryExpression.Op.AND,
                        new BinaryExpression(quantifiedVariableExpression, BinaryExpression.Op.MEMBER, setExpression));
            }
            else // add constraint (subset x A) for x: set A (or lone A, some A)
            {
                constraint = new BinaryExpression(constraint, BinaryExpression.Op.AND,
                        new BinaryExpression(quantifiedVariableExpression, BinaryExpression.Op.SUBSET, setExpression));

            }
        }
        constraint = new BinaryExpression(multiplicityConstraint, BinaryExpression.Op.AND, constraint);
        return constraint;
    }
}
