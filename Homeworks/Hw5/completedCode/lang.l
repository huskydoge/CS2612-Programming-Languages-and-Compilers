%option noyywrap yylineno
%option outfile="lexer.c" header-file="lexer.h"
%{
#include "lang.h"
#include "parser.h"
#include "lib.h"
%}

%%
"struct" {
    return TM_STRUCT;
}

"enum" {
    return TM_ENUM;
}

"union" {
    return TM_UNION;
}

"typedef" {
    return TM_TYPEDEF;
}

"int" {
    return TM_INT;
}

"char" {
    return TM_CHAR;
}

"*" {
    return TM_DEREF;
}

"[" {
    return TM_LEFT_SQUARE;
}

"]" {
    return TM_RIGHT_SQUARE;
}

"," {
    return TM_COMMA;
}

0|[1-9][0-9]* {
    yylval.n = build_nat(yytext, yyleng);
    return TM_NAT;
}

[_A-Za-z][_A-Za-z0-9]* {
    yylval.i = new_str(yytext, yyleng);
    return TM_IDENT;
}

";" {
    return TM_SEMICOL;
    }

"(" {
    return TM_LEFT_PAREN;
    }

")" {
    return TM_RIGHT_PAREN;
    }

"{" {
    return TM_LEFT_BRACE;
    }

"}" {
    return TM_RIGHT_BRACE;
    }


[ \t\n\r]    { };

.   {printf("%s",yytext);
     return -1; }
    


%%
