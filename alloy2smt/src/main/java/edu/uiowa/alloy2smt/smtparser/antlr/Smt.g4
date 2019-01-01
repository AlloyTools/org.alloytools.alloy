grammar Smt;

// parser rules

model : '(' 'model' sortDeclaration* functionDefinition* ')' ;

sortDeclaration :  '(' 'declare-sort' sortName arity ')' ;

functionDefinition : '(' 'define-fun' functionName '(' argument* ')' '(' sort ')' '(' term ')' ')' ;

argument : '(' argumentName sort ')' ;

sort :  sortName | tupleSort | setSort ;

setSort : 'Set' '(' sort ')' ;

tupleSort : 'Tuple' sort+ ;

sortName : Identifier ;

arity : Integer ;

functionName : Identifier ;

argumentName : Identifier ;

term :  integerConstant
        | tupleConstant
        | singletonConstant
        | unionConstant
        | atomConstant
        | emptySet ;

integerConstant : '-' Integer | Integer ;

tupleConstant : 'mkTuple' term+ ;

singletonConstant : 'singleton' '(' term ')' ;

unionConstant : 'union' ( '(' term ')' ) ( '(' term ')' ) ;

atomConstant : '@uc_Atom_' Integer;

emptySet : 'as' 'emptyset' '(' 'Set' '(' sort ')' ')' ;

// lexer rules
Identifier : IdentifierLetter (IdentifierLetter | Digit)* ;

IdentifierLetter : 'a'..'z'|'A'..'Z'|'_' ;

Integer : Digit+ ;

Digit : '0'..'9' ;

Comment :  ';' ~( '\r' | '\n' )* -> skip ;

Whitespace :  [ \t\r\n]+ -> skip ;