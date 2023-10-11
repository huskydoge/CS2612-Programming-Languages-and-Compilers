#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "lang.h"

union token_value val;

unsigned int build_nat(char * c, int len) {
  int s = 0, i = 0;
  for (i = 0; i < len; ++i) {
    if (s > 429496729) {
      printf("We cannot handle natural numbers greater than 4294967295.\n");
      exit(0);
    }
    if (s == 429496729 && c[i] > '5') {
      printf("We cannot handle natural numbers greater than 4294967295.\n");
      exit(0);
    }
    s = s * 10 + (c[i] - '0');
  }
  return s;
}

char * new_str(char * str, int len) {
  char * res = (char *) malloc(sizeof(char) * (len + 1));
  if (res == NULL) {
    printf("Failure in malloc.\n");
    exit(0);
  }
  strcpy(res, str);
  return res;
}

void print_token(enum token_class c) {
  switch (c) {
  case TOK_OR:
    printf("OR\n");
    break;
  case TOK_AND:
    printf("AND\n");
    break;
  case TOK_NOT:
    printf("NOT\n");
    break;
  case TOK_LT:
    printf("LT\n");
    break;
  case TOK_LE:
    printf("LE\n");
    break;
  case TOK_GT:
    printf("GT\n");
    break;
  case TOK_GE:
    printf("GE\n");
    break;
  case TOK_EQ:
    printf("EQ\n");
    break;
  case TOK_NE:
    printf("NE\n");
    break;
  case TOK_PLUS:
    printf("PLUS\n");
    break;
  case TOK_MINUS:
    printf("MINUS\n");
    break;
  case TOK_MUL:
    printf("MUL\n");
    break;
  case TOK_DIV:
    printf("DIV\n");
    break;
  case TOK_MOD:
    printf("AND\n");
    break;
  case TOK_ASGNOP:
    printf("ASGNOP\n");
    break;
  case TOK_LEFT_BRACE:
    printf("LEFT_BRACE\n");
    break;
  case TOK_RIGHT_BRACE:
    printf("RIGHT_BRACE\n");
    break;
  case TOK_LEFT_PAREN:
    printf("LEFT_PAREN\n");
    break;
  case TOK_RIGHT_PAREN:
    printf("RIGHT_PAREN\n");
    break;
  case TOK_SEMICOL:
    printf("SEMICOL\n");
    break;
  case TOK_NAT:
    printf("NAT(%d)\n",val.n);
    break;
  case TOK_IDENT:
    printf("IDENT(%s)\n",val.i);
    break;
  case TOK_VAR:
    printf("VAR\n");
    break;
  case TOK_IF:
    printf("IF\n");
    break;
  case TOK_THEN:
    printf("THEN\n");
    break;
  case TOK_ELSE:
    printf("ELSE\n");
    break;
  case TOK_WHILE:
    printf("WHILE\n");
    break;
  case TOK_DO:
    printf("DO\n");
    break;
  case TOK_MALLOC:
    printf("MALLOC\n");
    break;
  case TOK_RI:
    printf("RI\n");
    break;
  case TOK_RC:
    printf("RC\n");
    break;
  case TOK_WI:
    printf("WI\n");
    break;
  case TOK_WC:
    printf("WC\n");
    break;
  }
}
