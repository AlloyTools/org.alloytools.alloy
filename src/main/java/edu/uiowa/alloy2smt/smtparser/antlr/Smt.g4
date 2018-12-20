grammar Smt;

// parser rules

model : '(' 'model' declarations* definitions* ')' ;

declarations :  '(' 'declare-sort' sort arity ')';

definitions : '(' 'define-fun' functionName '(' arguments* ')' '(' sort ')' '(' term ')' ')';

arguments : '(' argumentName sort ')';

sort :  Identifier | 'Tuple' sort+ | 'Set' '(' sort ')' ;

arity: Integer;

functionName : Identifier;

argumentName : Identifier;

term:   Integer
        | '-' Integer
        | 'mkTuple' term+
        | 'singleton' '(' term ')'
        | 'union' ( '(' term ')' )+
        | '@uc_Atom_' Integer
        | 'as' 'emptyset' '(' 'Set' '(' sort ')' ')';

// lexer rules
Identifier : IdentifierLetter (IdentifierLetter | Digit)* ;

IdentifierLetter : 'a'..'z'|'A'..'Z'|'_' ;

Integer : Digit+ ;

Digit : '0'..'9' ;

Comment   :  ';' ~( '\r' | '\n' )* -> skip ;

Whitespace :  [ \t\r\n]+ -> skip ;