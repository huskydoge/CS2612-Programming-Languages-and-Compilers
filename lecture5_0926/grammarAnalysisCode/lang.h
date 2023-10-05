#ifndef LANG_H_INCLUDED
#define LANG_H_INCLUDED

#include <stdio.h>
#include <stdlib.h>

enum BinOpType {
  T_PLUS,
  T_MINUS,
  T_MUL,
  T_DIV,
  T_MOD,
  T_LT,
  T_GT,
  T_LE,
  T_GE,
  T_EQ,
  T_NE,
  T_AND,
  T_OR
};

enum UnOpType {
  T_UMINUS,
  T_NOT
};

enum ExprType {
  T_CONST = 0,
  T_VAR,
  T_BINOP,
  T_UNOP,
  T_DEREF,
  T_MALLOC,
  T_RI,
  T_RC
};

enum CmdType {
  T_DECL = 0,
  T_ASGN,
  T_SEQ,
  T_IF,
  T_WHILE,
  T_WI,
  T_WC
};

struct expr {
  enum ExprType t;
  union {
    struct {unsigned int value; } CONST;
    struct {char * name; } VAR;
    struct {enum BinOpType op; struct expr * left; struct expr * right; } BINOP;
    struct {enum UnOpType op; struct expr * arg; } UNOP;
    struct {struct expr * arg; } DEREF;
    struct {struct expr * arg; } MALLOC;
    struct {void * none; } RI;
    struct {void * none; } RC;
  } d;
};

struct cmd {
  enum CmdType t;
  union {
    struct {char * name; } DECL;
    struct {struct expr * left; struct expr * right; } ASGN;
    struct {struct cmd * left; struct cmd * right; } SEQ;
    struct {struct expr * cond; struct cmd * left; struct cmd * right; } IF;
    struct {struct expr * cond; struct cmd * body; } WHILE;
    struct {struct expr * arg; } WI;
    struct {struct expr * arg; } WC;
  } d;
};

struct expr * TConst(unsigned int value);
struct expr * TVar(char * name);
struct expr * TBinOp(enum BinOpType op, struct expr * left, struct expr * right);
struct expr * TUnOp(enum UnOpType op, struct expr * arg);
struct expr * TDeref(struct expr * arg);
struct expr * TMalloc(struct expr * arg);
struct expr * TReadInt();
struct expr * TReadChar();
struct cmd * TDecl(char * name);
struct cmd * TAsgn(struct expr * left, struct expr * right);
struct cmd * TSeq(struct cmd * left, struct cmd * right);
struct cmd * TIf(struct expr * cond, struct cmd * left, struct cmd * right);
struct cmd * TWhile(struct expr * cond, struct cmd * body);
struct cmd * TWriteInt(struct expr * arg);
struct cmd * TWriteChar(struct expr * arg);

void print_binop(enum BinOpType op);
void print_unop(enum UnOpType op);
void print_expr(struct expr * e);
void print_cmd(struct cmd * c);

unsigned int build_nat(char * c, int len);
char * new_str(char * str, int len);

#endif // LANG_H_INCLUDED
