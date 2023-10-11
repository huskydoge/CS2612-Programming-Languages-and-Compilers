%option noyywrap yylineno
%option outfile="lexer.c" header-file="lexer.h"
%{
#include "lang.h"
%}

%%

0|[1-9][0-9]* {
    val.n = build_nat(yytext, yyleng);
    return TOK_NAT;
}

"var" {
    return TOK_VAR;
}

"if" {
    return TOK_IF;
}

"then" {
    return TOK_THEN;
}

"else" {
    return TOK_ELSE;
}

"while" {
    return TOK_WHILE;
}

"do" {
    return TOK_DO;
}

"malloc" {
    return TOK_MALLOC;
}

"read_int" {
    return TOK_RI;
}

"read_char" {
    return TOK_RC;
}

"write_int" {
    return TOK_WI;
}

"write_char" {
    return TOK_WC;
}

[_A-Za-z][_A-Za-z0-9]* {
    val.i = new_str(yytext, yyleng);
    return TOK_IDENT;
}

";" {
    return TOK_SEMICOL;
    }

"(" {
    return TOK_LEFT_PAREN;
    }

")" {
    return TOK_RIGHT_PAREN;
    }

"{" {
    return TOK_LEFT_BRACE;
    }

"}" {
    return TOK_RIGHT_BRACE;
    }

"+" {
    return TOK_PLUS;
    }

"-" {
    return TOK_MINUS;
    }

"*" {
    return TOK_MUL;
    }

"/" {
    return TOK_DIV;
    }

"%" {
    return TOK_MOD;
    }

"<" {
    return TOK_LT;
    }

">" {
    return TOK_GT;
    }

"<=" {
    return TOK_LE;
    }

">=" {
    return TOK_GE;
    }

"==" {
    return TOK_EQ;
    }

"!=" {
    return TOK_NE;
    }

"=" {
    return TOK_ASGNOP;
    }

"&&" {
    return TOK_AND;
    }

"||" {
    return TOK_OR;
    }

"!" {
    return TOK_NOT;
    }

[ \t\n\r]    { };

.   {printf("%s",yytext);
     return -1; }
%%
