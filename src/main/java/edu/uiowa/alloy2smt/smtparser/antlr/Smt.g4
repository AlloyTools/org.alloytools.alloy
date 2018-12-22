grammar Smt;

// parser rules

model: '(' 'model' sortDeclaration* definition* ')' ;

sortDeclaration:  '(' 'declare-sort' sortName arity ')';

definition: '(' 'define-fun' functionName '(' argument* ')' '(' sort ')' '(' term ')' ')';

argument: '(' argumentName sort ')';

sort:  sortName | tupleSort | setSort ;

setSort: 'Set' '(' sort ')';

tupleSort: 'Tuple' sort+ ;

sortName: Identifier;

arity: Integer;

functionName: Identifier;

argumentName: Identifier;

term:   Integer
        | '-' Integer
        | 'mkTuple' term+
        | 'singleton' '(' term ')'
        | 'union' ( '(' term ')' )+
        | '@uc_Atom_' Integer
        | 'as' 'emptyset' '(' 'Set' '(' sort ')' ')';

// lexer rules
Identifier: IdentifierLetter (IdentifierLetter | Digit)* ;

IdentifierLetter: 'a'..'z'|'A'..'Z'|'_' ;

Integer: Digit+ ;

Digit: '0'..'9' ;

Comment  :  ';' ~( '\r' | '\n' )* -> skip ;

Whitespace:  [\t\r\n]+ -> skip ;