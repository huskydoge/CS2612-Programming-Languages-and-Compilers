#include <stdio.h>
#include "lang.h"
#include "lexer.h"
#include "parser.h"

extern struct glob_item_list * root;
int yyparse();

int main(int argc, char * * argv) {
  if (argc == 1) {
    printf("Error, not enough arguments!\n");
    return 0;
  }
  if (argc >= 3) {
    printf("Error, too many arguments!\n");
    return 0;
  }
  yyin = fopen(argv[1], "rb");
  if (yyin == NULL) {
    printf("File %s can't be opened.\n", argv[1]);
    return 0;
  }
  yyparse();
  fclose(yyin);
  print_glob_item_list(root);
}
