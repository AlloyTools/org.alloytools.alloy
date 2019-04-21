grammar Smt;

// parser rules

model : '(' 'model' sortDeclaration* functionDefinition* ')' ;

sortDeclaration :  '(' 'declare-sort' sortName arity ')' ;

functionDefinition : '(' 'define-fun' functionName '(' argument* ')' ('(' sort ')'| sort)
                        expression ')' ;

argument : '(' argumentName sort ')' ;

sort :  sortName | tupleSort | setSort ;

setSort : 'Set' '(' sort ')' ;

tupleSort : 'Tuple' sort+ ;

sortName : Identifier ;

arity : Integer ;

functionName : Identifier ;

argumentName : Identifier ;

expression :    constant
                | variable
                | unaryExpression
                | binaryExpression
                | ternaryExpression
                | multiArityExpression
                | '(' expression ')';


unaryExpression : UnaryOperator expression ;

binaryExpression : BinaryOperator expression expression ;

ternaryExpression : TernaryOperator expression expression expression ;

multiArityExpression :  MultiArityOperator expression+ ;

variable : Identifier;

constant :  integerConstant
            | uninterpretedConstant
            | emptySet ;

integerConstant : '-' Integer | Integer ;

uninterpretedConstant : (AtomPrefix | UninterpretedIntPrefix) Integer;

emptySet : 'as' 'emptyset' '(' 'Set' '(' sort ')' ')' ;

// lexer rules
UnaryOperator : 'not' | 'singleton' | 'complement' | 'transpose' | 'tclosure' ;

BinaryOperator : '=' | '>' | '>=' | '<' | '<='
                | '+' | '-' | '*' | '/' | 'mod'
                | 'or' | 'and' | '=>'
                | 'union' | 'intersection' | 'setminus' | 'member' | 'subset'
                | 'join' | 'product' ;

TernaryOperator : 'ite' ;

MultiArityOperator : 'mkTuple' | 'insert' | 'distinct' ;

AtomPrefix : '@uc_Atom_';

UninterpretedIntPrefix : '@uc_UninterpretedInt_' ;

Identifier : IdentifierLetter (IdentifierLetter | Digit)* ;

IdentifierLetter : 'a'..'z'|'A'..'Z'|'_' ;

Integer : Digit+ ;

Digit : '0'..'9' ;

Comment :  ';' ~( '\r' | '\n' )* -> skip ;

Whitespace :  [ \t\r\n]+ -> skip ;