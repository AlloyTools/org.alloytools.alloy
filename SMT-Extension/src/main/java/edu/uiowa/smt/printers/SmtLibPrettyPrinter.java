package edu.uiowa.smt.printers;

import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;

import java.util.Map;

public class SmtLibPrettyPrinter extends SmtLibPrinter
{
    private int tabsCount = 0;

    private void printTabs()
    {
        for (int i = 0; i < tabsCount; i++)
        {
            stringBuilder.append(" ");
        }
    }

    public SmtLibPrettyPrinter(SmtSettings smtSettings)
    {
        super(smtSettings);
    }

    public SmtLibPrettyPrinter()
    {
        super();
    }

    @Override
    public void visit(UnaryExpression unaryExpression)
    {
        tabsCount++;
        stringBuilder.append("\n");
        printTabs();
        stringBuilder.append("(" + unaryExpression.getOP() + " ");
        tabsCount++;
        this.visit(unaryExpression.getExpression());
        stringBuilder.append(")");
        tabsCount -= 2;

    }

    @Override
    public void visit(BinaryExpression binaryExpression)
    {
        if(binaryExpression.getOp() != BinaryExpression.Op.TUPSEL)
        {
            tabsCount++;
            stringBuilder.append("\n");
            printTabs();
            stringBuilder.append("(" + binaryExpression.getOp() + " ");
            tabsCount++;
            this.visit(binaryExpression.getA());
            stringBuilder.append(" ");
            this.visit(binaryExpression.getB());
            stringBuilder.append(")");
            tabsCount -= 2;
        }
        else
        {
            stringBuilder.append("((_ " + binaryExpression.getOp() + " ");
            stringBuilder.append(((IntConstant)binaryExpression.getA()).getValue());
            stringBuilder.append(") ");
            this.visit(binaryExpression.getB());
            stringBuilder.append(")");
        }
    }

    @Override
    public void visit(MultiArityExpression multiArityExpression)
    {
        tabsCount++;
        stringBuilder.append("\n");
        printTabs();
        stringBuilder.append("(" + multiArityExpression.getOp() + " ");
        tabsCount++;
        if(multiArityExpression.getExpressions().size() == 1)
        {
            this.visit(multiArityExpression.getExpressions().get(0));
        }
        else if(multiArityExpression.getExpressions().size() > 1)
        {
            for (int i = 0; i < multiArityExpression.getExpressions().size()-1; ++i)
            {
                this.visit(multiArityExpression.getExpressions().get(i));
                stringBuilder.append(" ");
            }
            this.visit(multiArityExpression.getExpressions().get(multiArityExpression.getExpressions().size()-1));
        }
        else
        {
            throw new RuntimeException("");
        }
        stringBuilder.append(")");
        tabsCount -= 2;
    }

    @Override
    public void visit(QuantifiedExpression quantifiedExpression)
    {
        quantifiedExpression = optimize(quantifiedExpression);
        tabsCount++;
        stringBuilder.append("\n");
        printTabs();
        stringBuilder.append("(" + quantifiedExpression.getOp() + " (");
        for (VariableDeclaration boundVariable: quantifiedExpression.getVariables())
        {
            this.visit(boundVariable);
        }
        stringBuilder.append(") ");
        tabsCount ++;
        this.visit(quantifiedExpression.getExpression());
        stringBuilder.append(")");
        tabsCount -= 2;
    }

    @Override
    public void visit(LetExpression let)
    {
        tabsCount++;
        stringBuilder.append("\n");
        printTabs();
        stringBuilder.append("(let (");
        for(Map.Entry<VariableDeclaration, Expression> letVar : let.getLetVariables().entrySet())
        {
            tabsCount++;
            stringBuilder.append("\n");
            printTabs();
            stringBuilder.append("(");
            stringBuilder.append(TranslatorUtils.sanitizeWithBars(letVar.getKey())).append(" ");
            this.visit(letVar.getValue());
            stringBuilder.append(")");
            tabsCount--;
        }
        stringBuilder.append(") ");
        tabsCount ++;
        this.visit(let.getExpression());
        stringBuilder.append(")");
        tabsCount -= 2;
    }

    @Override
    public void visit(Expression expression)
    {
        super.visit(expression);
        if(!expression.getComment().isEmpty())
        {
            stringBuilder.append("; " + expression.getComment() + "\n");
            printTabs();
        }
    }
}
