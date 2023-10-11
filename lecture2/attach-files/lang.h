#ifndef LANG_H_INCLUDED
#define LANG_H_INCLUDED

enum token_class {
  // 运算符
    TOK_OR = 1, TOK_AND, TOK_NOT,
    TOK_LT, TOK_LE, TOK_GT, TOK_GE, TOK_EQ, TOK_NE,
    TOK_PLUS, TOK_MINUS, TOK_MUL, TOK_DIV, TOK_MOD,
  // 赋值符号
    TOK_ASGNOP,
  // 间隔符号
    TOK_LEFT_BRACE, TOK_RIGHT_BRACE,
    TOK_LEFT_PAREN, TOK_RIGHT_PAREN,
    TOK_SEMICOL,
  // 自然数
    TOK_NAT,
  // 变量名
    TOK_IDENT,
  // 保留字
    TOK_VAR, TOK_IF, TOK_THEN, TOK_ELSE, TOK_WHILE, TOK_DO,
  // 内置函数名
    TOK_MALLOC, TOK_RI, TOK_RC, TOK_WI, TOK_WC
};

union token_value {
  unsigned int n;
  char * i;
  void * none;
};

extern union token_value val;
unsigned int build_nat(char * c, int len);
char * new_str(char * str, int len);
void print_token(enum token_class c);

#endif // LANG_H_INCLUDED
