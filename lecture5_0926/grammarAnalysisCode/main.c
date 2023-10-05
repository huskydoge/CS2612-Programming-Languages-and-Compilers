#include <stdio.h>
#include "lang.h"
#include "lexer.h"
#include "parser.h"

extern struct cmd * root;
int yyparse();

int main(int argc, char **argv) {
    yyin = stdin;
    yyparse();
    fclose(stdin);
    print_cmd(root);
}
