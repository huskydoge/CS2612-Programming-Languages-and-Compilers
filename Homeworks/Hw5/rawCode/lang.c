#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "lang.h"

struct type_list * new_type_list_ptr() {
  struct type_list * res =
    (struct type_list *) malloc(sizeof(struct type_list));
  if (res == NULL) {
    printf("Failure in malloc.\n");
    exit(0);
  }
  return res;
}

struct enum_ele_list * new_enum_ele_list_ptr() {
  struct enum_ele_list * res =
    (struct enum_ele_list *) malloc(sizeof(struct enum_ele_list));
  if (res == NULL) {
    printf("Failure in malloc.\n");
    exit(0);
  }
  return res;
}

struct left_type * new_left_type_ptr() {
  struct left_type * res =
    (struct left_type *) malloc(sizeof(struct left_type));
  if (res == NULL) {
    printf("Failure in malloc.\n");
    exit(0);
  }
  return res;
}

struct var_decl_expr * new_var_decl_expr_ptr() {
  struct var_decl_expr * res =
    (struct var_decl_expr *) malloc(sizeof(struct var_decl_expr));
  if (res == NULL) {
    printf("Failure in malloc.\n");
    exit(0);
  }
  return res;
}

struct glob_item * new_glob_item_ptr() {
  struct glob_item * res =
    (struct glob_item *) malloc(sizeof(struct glob_item));
  if (res == NULL) {
    printf("Failure in malloc.\n");
    exit(0);
  }
  return res;
}

struct glob_item_list * new_glob_item_list_ptr() {
  struct glob_item_list * res =
    (struct glob_item_list *) malloc(sizeof(struct glob_item_list));
  if (res == NULL) {
    printf("Failure in malloc.\n");
    exit(0);
  }
  return res;
}

struct type_list * TTNil() {
  return NULL;
}

struct type_list * TTCons(struct left_type * t, struct var_decl_expr * e, 
                           struct type_list * next) {
  struct type_list * res = new_type_list_ptr();
  res -> t = t;
  res -> e = e;
  res -> next = next;
  return res;
}

struct enum_ele_list * TENil() {
  return NULL;
}

struct enum_ele_list * TECons(char * name, struct enum_ele_list * next) {
  struct enum_ele_list * res = new_enum_ele_list_ptr();
  res -> name = name;
  res -> next = next;
  return res;
}

struct left_type * TStructType(char * name) {
  struct left_type * res = new_left_type_ptr();
  res -> t = T_STRUCT_TYPE;
  res -> d.STRUCT_TYPE.name = name;
  return res;
}

struct left_type * TNewStructType(char * name, struct type_list * fld) {
  struct left_type * res = new_left_type_ptr();
  res -> t = T_NEW_STRUCT_TYPE;
  res -> d.NEW_STRUCT_TYPE.name = name;
  res -> d.NEW_STRUCT_TYPE.fld = fld;
  return res;
}

struct left_type * TUnionType(char * name) {
  struct left_type * res = new_left_type_ptr();
  res -> t = T_UNION_TYPE;
  res -> d.UNION_TYPE.name = name;
  return res;
}

struct left_type * TNewUnionType(char * name, struct type_list * fld) {
  struct left_type * res = new_left_type_ptr();
  res -> t = T_NEW_UNION_TYPE;
  res -> d.NEW_UNION_TYPE.name = name;
  res -> d.NEW_UNION_TYPE.fld = fld;
  return res;
}

struct left_type * TEnumType(char * name) {
  struct left_type * res = new_left_type_ptr();
  res -> t = T_ENUM_TYPE;
  res -> d.ENUM_TYPE.name = name;
  return res;
}

struct left_type * TNewEnumType(char * name, struct enum_ele_list * ele) {
  struct left_type * res = new_left_type_ptr();
  res -> t = T_NEW_ENUM_TYPE;
  res -> d.NEW_ENUM_TYPE.name = name;
  res -> d.NEW_ENUM_TYPE.ele = ele;
  return res;
}

struct left_type * TIntType() {
  struct left_type * res = new_left_type_ptr();
  res -> t = T_INT_TYPE;
  return res;
}

struct left_type * TCharType() {
  struct left_type * res = new_left_type_ptr();
  res -> t = T_CHAR_TYPE;
  return res;
}

struct left_type * TDefinedType(char * name) {
  struct left_type * res = new_left_type_ptr();
  res -> t = T_DEFINED_TYPE;
  res -> d.DEFINED_TYPE.name = name;
  return res;
}

struct var_decl_expr * TOrigType(char * name) {
  struct var_decl_expr * res = new_var_decl_expr_ptr();
  res -> t = T_ORIG_TYPE;
  res -> d.ORIG_TYPE.name = name;
  return res;
}

struct var_decl_expr * TPtrType(struct var_decl_expr * base) {
  struct var_decl_expr * res = new_var_decl_expr_ptr();
  res -> t = T_PTR_TYPE;
  res -> d.PTR_TYPE.base = base;
  return res;
}

struct var_decl_expr * TArrayType(struct var_decl_expr * base,
                                  unsigned int size) {
  struct var_decl_expr * res = new_var_decl_expr_ptr();
  res -> t = T_ARRAY_TYPE;
  res -> d.ARRAY_TYPE.base = base;
  res -> d.ARRAY_TYPE.size = size;
  return res;
}

struct var_decl_expr * TFuncType(struct var_decl_expr * ret,
                                 struct type_list * args) {
  struct var_decl_expr * res = new_var_decl_expr_ptr();
  res -> t = T_FUNC_TYPE;
  res -> d.FUNC_TYPE.ret = ret;
  res -> d.FUNC_TYPE.args = args;
  return res;
}

struct glob_item * TStructDef(char * name, struct type_list * fld) {
  struct glob_item * res = new_glob_item_ptr();
  res -> t = T_STRUCT_DEF;
  res -> d.STRUCT_DEF.name = name;
  res -> d.STRUCT_DEF.fld = fld;
  return res;
}

struct glob_item * TStructDecl(char * name) {
  struct glob_item * res = new_glob_item_ptr();
  res -> t = T_STRUCT_DECL;
  res -> d.STRUCT_DECL.name = name;
  return res;
}

struct glob_item * TUnionDef(char * name, struct type_list * fld) {
  struct glob_item * res = new_glob_item_ptr();
  res -> t = T_UNION_DEF;
  res -> d.UNION_DEF.name = name;
  res -> d.UNION_DEF.fld = fld;
  return res;
}

struct glob_item * TUnionDecl(char * name) {
  struct glob_item * res = new_glob_item_ptr();
  res -> t = T_UNION_DECL;
  res -> d.UNION_DECL.name = name;
  return res;
}

struct glob_item * TEnumDef(char * name, struct enum_ele_list * ele) {
  struct glob_item * res = new_glob_item_ptr();
  res -> t = T_ENUM_DEF;
  res -> d.ENUM_DEF.name = name;
  res -> d.ENUM_DEF.ele = ele;
  return res;
}

struct glob_item * TEnumDecl(char * name) {
  struct glob_item * res = new_glob_item_ptr();
  res -> t = T_ENUM_DECL;
  res -> d.ENUM_DECL.name = name;
  return res;
}

struct glob_item * TTypeDef(struct left_type * t, struct var_decl_expr * e) {
  struct glob_item * res = new_glob_item_ptr();
  res -> t = T_TYPE_DEF;
  res -> d.TYPE_DEF.t = t;
  res -> d.TYPE_DEF.e = e;
  return res;
}

struct glob_item * TVarDef(struct left_type * t, struct var_decl_expr * e) {
  struct glob_item * res = new_glob_item_ptr();
  res -> t = T_VAR_DEF;
  res -> d.VAR_DEF.t = t;
  res -> d.VAR_DEF.e = e;
  return res;
}

struct glob_item_list * TGNil() {
  return NULL;
}

struct glob_item_list * TGCons(struct glob_item * data,
                               struct glob_item_list * next) {
  struct glob_item_list * res = new_glob_item_list_ptr();
  res -> data = data;
  res -> next = next;
  return res;
}

int indent = 0;

void print_spaces() {
  int i;
  for (i = 0; i < indent; ++ i) {
    printf("  ");
  }
}

void print_type_list_as_fields(struct type_list * fld) {
  if (fld == NULL) {
    return;
  }
  print_spaces();
  printf("Field:\n");
  indent ++;
  print_left_type(fld -> t);
  print_var_decl_expr_for_field(fld -> e);
  indent --;
  print_type_list_as_fields(fld -> next);
}

void print_type_list_as_argument_types(struct type_list * args) {
  if (args == NULL) {
    return;
  }
  print_spaces();
  printf("Argument type:\n");
  indent ++;
  print_left_type(args -> t);
  print_annon_var_decl_expr(args -> e);
  indent --;
  print_type_list_as_argument_types(args -> next);
}

void print_enum_ele_list(struct enum_ele_list * ele) {
  if (ele == NULL) {
    return;
  }
  printf(" %s", ele -> name);
  print_enum_ele_list(ele -> next);
}

void print_left_type(struct left_type * t) {
  switch (t -> t) {
  case T_STRUCT_TYPE:
    print_spaces();
    printf("Left type: struct %s\n", t -> d.STRUCT_TYPE.name);
    return;
  case T_NEW_STRUCT_TYPE:
    print_spaces();
    if (t -> d.NEW_STRUCT_TYPE.name == NULL) {
      printf("Left type: new annonymous struct\n");
    }
    else {
      printf("Left type: new struct %s\n", t -> d.NEW_STRUCT_TYPE.name);
    }
    indent ++;
    print_type_list_as_fields(t -> d.NEW_STRUCT_TYPE.fld);
    indent --;
    return;
  case T_UNION_TYPE:
    print_spaces();
    printf("Left type: union %s\n", t -> d.UNION_TYPE.name);
    return;
  case T_NEW_UNION_TYPE:
    print_spaces();
    if (t -> d.NEW_UNION_TYPE.name == NULL) {
      printf("Left type: new annonymous union\n");
    }
    else {
      printf("Left type: new union %s\n", t -> d.NEW_UNION_TYPE.name);
    }
    indent ++;
    print_type_list_as_fields(t -> d.NEW_UNION_TYPE.fld);
    indent --;
    return;
  case T_ENUM_TYPE:
    print_spaces();
    printf("Left type: enum %s\n", t -> d.ENUM_TYPE.name);
    return;
  case T_NEW_ENUM_TYPE:
    print_spaces();
    if (t -> d.NEW_ENUM_TYPE.name == NULL) {
      printf("Left type: new annonymous enum\n");
    }
    else {
      printf("Left type: new enum %s (", t -> d.NEW_ENUM_TYPE.name);
      print_enum_ele_list(t -> d.NEW_ENUM_TYPE.ele);
      printf(" )\n");
    }
    return;
  case T_INT_TYPE:
    print_spaces();
    printf("Left type: int\n");
    return;
  case T_CHAR_TYPE:
    print_spaces();
    printf("Left type: char\n");
    return;
  case T_DEFINED_TYPE:
    print_spaces();
    printf("Left type: defined type %s\n", t -> d.DEFINED_TYPE.name);
    return;
  }
}

enum PrintRetType {
  T_ORIG_TYPE_RETURN,
  T_FUNC_TYPE_RETURN
};

struct print_ret {
  enum PrintRetType t;
  union {
    char * name;
    struct var_decl_expr * e;
  } d;
};

struct print_ret * OrigTypeReturn(char * name) {
  struct print_ret * res =
    (struct print_ret *) malloc (sizeof (struct print_ret));
  res -> t = T_ORIG_TYPE_RETURN;
  res -> d.name = name;
  return res;
}

struct print_ret * FuncTypeReturn(struct var_decl_expr * e) {
  struct print_ret * res =
    (struct print_ret *) malloc (sizeof (struct print_ret));
  res -> t = T_FUNC_TYPE_RETURN;
  res -> d.e = e;
  return res;
}

struct print_ret * print_var_decl_expr_rec(struct var_decl_expr * e) {
  struct print_ret * res;
  switch (e -> t) {
  case T_ORIG_TYPE:
    return OrigTypeReturn(e -> d.ORIG_TYPE.name);
  case T_PTR_TYPE:
    res = print_var_decl_expr_rec(e -> d.PTR_TYPE.base);
    printf("pointer of ");
    return res;
  case T_ARRAY_TYPE:
    res = print_var_decl_expr_rec(e -> d.ARRAY_TYPE.base);
    printf("array[%d] of ", e -> d.ARRAY_TYPE.size);
    return res;
  case T_FUNC_TYPE:
    return FuncTypeReturn(e);
  }
}

char * print_var_decl_expr_rec2(struct var_decl_expr * e) {
  struct print_ret * r = print_var_decl_expr_rec(e);
  char * res;
  switch (r -> t) {
  case T_ORIG_TYPE_RETURN:
    res = r -> d.name;
    printf("the LHS type\n");
    free(r);
    return res;
  case T_FUNC_TYPE_RETURN:
    printf("the following function type\n");
    indent ++;
    print_spaces();
    printf("Return type: ");
    res = print_var_decl_expr_rec2(r -> d.e -> d.FUNC_TYPE.ret);
    print_type_list_as_argument_types(r -> d.e -> d.FUNC_TYPE.args);
    indent --;
    free(r);
    return res;
  }
}

void print_var_decl_expr_for_var(struct var_decl_expr * e) {
  print_spaces();
  printf("Right type: ");
  char * name = print_var_decl_expr_rec2(e);
  print_spaces();
  printf("Var name: %s\n", name);
}

void print_var_decl_expr_for_field(struct var_decl_expr * e) {
  print_spaces();
  printf("Right type: ");
  char * name = print_var_decl_expr_rec2(e);
  print_spaces();
  printf("Field name: %s\n", name);
}

void print_var_decl_expr_for_typedef(struct var_decl_expr * e) {
  print_spaces();
  printf("Right type: ");
  char * name = print_var_decl_expr_rec2(e);
  print_spaces();
  printf("Type name: %s\n", name);
}

void print_annon_var_decl_expr(struct var_decl_expr * e) {
  print_spaces();
  printf("Right type: ");
  char * name = print_var_decl_expr_rec2(e);
}

void print_glob_item(struct glob_item * g) {
  switch (g -> t) {
  case T_STRUCT_DEF:
    printf("struct definition: %s\n", g -> d.STRUCT_DEF.name);
    indent ++;
    print_type_list_as_fields(g -> d.STRUCT_DEF.fld);
    indent --;
    return;
  case T_STRUCT_DECL:
    printf("struct declaration: %s\n", g -> d.STRUCT_DECL.name);
    return;
  case T_UNION_DEF:
    printf("union definition: %s\n", g -> d.UNION_DEF.name);
    indent ++;
    print_type_list_as_fields(g -> d.UNION_DEF.fld);
    indent --;
    return;
  case T_UNION_DECL:
    printf("union declaration: %s\n", g -> d.UNION_DECL.name);
    return;
  case T_ENUM_DEF:
    printf("enum definition: %s (", g -> d.ENUM_DEF.name);
    print_enum_ele_list(g -> d.ENUM_DEF.ele);
    printf(" )\n");
    return;
  case T_ENUM_DECL:
    printf("enum declaration: %s\n", g -> d.ENUM_DECL.name);
    return;
  case T_TYPE_DEF:
    printf("typedef:\n");
    indent ++;
    print_left_type(g -> d.TYPE_DEF.t);
    print_var_decl_expr_for_typedef(g -> d.TYPE_DEF.e);
    indent --;
    return;
  case T_VAR_DEF:
    printf("var definition:\n");
    indent ++;
    print_left_type(g -> d.VAR_DEF.t);
    print_var_decl_expr_for_var(g -> d.VAR_DEF.e);
    indent --;
    return;
  }
}

void print_glob_item_list(struct glob_item_list * gs) {
  if (gs == NULL) {
    return;
  }
  print_glob_item(gs -> data);
  print_glob_item_list(gs -> next);
}

