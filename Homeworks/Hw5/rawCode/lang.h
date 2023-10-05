#ifndef LANG_H_INCLUDED
#define LANG_H_INCLUDED

#include <stdio.h>
#include <stdlib.h>
#include "lib.h"

enum LeftCTypeType {
  T_STRUCT_TYPE,
  T_NEW_STRUCT_TYPE,
  T_UNION_TYPE,
  T_NEW_UNION_TYPE,
  T_ENUM_TYPE,
  T_NEW_ENUM_TYPE,
  T_INT_TYPE,
  T_CHAR_TYPE,
  T_DEFINED_TYPE
};

enum VarDeclType {
  T_ORIG_TYPE,
  T_PTR_TYPE,
  T_ARRAY_TYPE,
  T_FUNC_TYPE
};

enum GlobItemType {
  T_STRUCT_DEF,
  T_STRUCT_DECL,
  T_UNION_DEF,
  T_UNION_DECL,
  T_ENUM_DEF,
  T_ENUM_DECL,
  T_TYPE_DEF,
  T_VAR_DEF
};

struct left_type;
  // left_type 表示类型声明左侧的类型，如struct、union、enum与基本类型
struct var_decl_expr;
  // var_decl_expr 表示类型声明右侧用于表达指针、数组等类型信息的表达式
  // var_decl_expr 可以含有一个变量名，也可以不包含任何变量名

struct type_list {
  struct left_type * t;
  struct var_decl_expr * e;
  struct type_list * next;
};
  // type_list 可以用于表示 struct与union 的域，以及函数的参数类型列表
  // 用于前者时，类型中的变量名就是域的名字；用于后者时，类型中可以没有变量名

struct enum_ele_list {
  char * name;
  struct enum_ele_list * next;
};

struct left_type {
  enum LeftCTypeType t;
  union {
    struct {char * name; } STRUCT_TYPE;
    struct {char * name; struct type_list * fld; } NEW_STRUCT_TYPE;
      // name = NULL 表示这是匿名 struct （只适用于NEW_STRUCT_TYPE情形）
    struct {char * name; } UNION_TYPE;
    struct {char * name; struct type_list * fld; } NEW_UNION_TYPE;
      // name = NULL 表示这是匿名 union （只适用于NEW_UNION_TYPE情形）
    struct {char * name; } ENUM_TYPE;
    struct {char * name; struct enum_ele_list * ele; } NEW_ENUM_TYPE;
      // name = NULL 表示这是匿名 enum （只适用于NEW_ENUM_TYPE情形）
    struct {void * none; } INT_TYPE;
    struct {void * none; } CHAR_TYPE;
    struct {char * name; } DEFINED_TYPE;
  } d;
};

struct var_decl_expr {
  enum VarDeclType t;
  union {
    struct { char * name; } ORIG_TYPE;
    struct { struct var_decl_expr * base; } PTR_TYPE;
    struct { struct var_decl_expr * base; unsigned int size; } ARRAY_TYPE;
    struct { struct var_decl_expr * ret; struct type_list * args; } FUNC_TYPE;
  } d;
};

struct glob_item {
  enum GlobItemType t;
  union {
    struct { char * name; struct type_list * fld; } STRUCT_DEF;
    struct { char * name; } STRUCT_DECL;
    struct { char * name; struct type_list * fld; } UNION_DEF;
    struct { char * name; } UNION_DECL;
    struct { char * name; struct enum_ele_list * ele; } ENUM_DEF;
    struct { char * name; } ENUM_DECL;
    struct { struct left_type * t; struct var_decl_expr * e; } TYPE_DEF;
    struct { struct left_type * t; struct var_decl_expr * e; } VAR_DEF;
  } d;
};

struct glob_item_list {
  struct glob_item * data;
  struct glob_item_list * next;
};

struct type_list * TTNil();
struct type_list * TTCons(struct left_type * t, struct var_decl_expr * e, 
                           struct type_list * next);
struct enum_ele_list * TENil();
struct enum_ele_list * TECons(char * name, struct enum_ele_list * next);
struct left_type * TStructType(char * name);
struct left_type * TNewStructType(char * name, struct type_list * fld);
struct left_type * TUnionType(char * name);
struct left_type * TNewUnionType(char * name, struct type_list * fld);
struct left_type * TEnumType(char * name);
struct left_type * TNewEnumType(char * name, struct enum_ele_list * ele);
struct left_type * TIntType();
struct left_type * TCharType();
struct left_type * TDefinedType(char * name);
struct var_decl_expr * TOrigType(char * name);
struct var_decl_expr * TPtrType(struct var_decl_expr * base);
struct var_decl_expr * TArrayType(struct var_decl_expr * base,
                                  unsigned int size);
struct var_decl_expr * TFuncType(struct var_decl_expr * ret,
                                 struct type_list * args);
struct glob_item * TStructDef(char * name, struct type_list * fld);
struct glob_item * TStructDecl(char * name);
struct glob_item * TUnionDef(char * name, struct type_list * fld);
struct glob_item * TUnionDecl(char * name);
struct glob_item * TEnumDef(char * name, struct enum_ele_list * ele);
struct glob_item * TEnumDecl(char * name);
struct glob_item * TTypeDef(struct left_type * t, struct var_decl_expr * e);
struct glob_item * TVarDef(struct left_type * t, struct var_decl_expr * e);
struct glob_item_list * TGNil();
struct glob_item_list * TGCons(struct glob_item * data,
                               struct glob_item_list * next);

void print_type_list_as_fields(struct type_list * fld);
void print_type_list_as_argument_types(struct type_list * fld);
void print_enum_ele_list(struct enum_ele_list * ele);
void print_left_type(struct left_type * t);
void print_var_decl_expr_for_var(struct var_decl_expr * e);
void print_var_decl_expr_for_typedef(struct var_decl_expr * e);
void print_var_decl_expr_for_field(struct var_decl_expr * e);
void print_annon_var_decl_expr(struct var_decl_expr * e);
void print_glob_item(struct glob_item * g);
void print_glob_item_list(struct glob_item_list * gs);

#endif // LANG_H_INCLUDED
