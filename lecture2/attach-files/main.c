#include "lang.h"
#include "lexer.h"

int main() {
  enum token_class c;
  while (1) {
    c = yylex();
    if (c != 0) {
      print_token(c);
    }
    else {
      break;
    }
  }
}
