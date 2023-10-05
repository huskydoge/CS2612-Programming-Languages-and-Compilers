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
struct var_decl_expr;

struct type_list {
  struct left_type * t;
  struct var_decl_expr * e;
  struct type_list * next;
};

struct enum_ele_list {
  char * name;
  struct enum_ele_list * next;
};

struct left_type {
  enum LeftCTypeType t;
  union {
    struct {char * name; } STRUCT_TYPE;
    struct {char * name; struct type_list * fld; } NEW_STRUCT_TYPE;
    struct {char * name; } UNION_TYPE;
    struct {char * name; struct type_list * fld; } NEW_UNION_TYPE;
    struct {char * name; } ENUM_TYPE;
    struct {char * name; struct enum_ele_list * ele; } NEW_ENUM_TYPE;
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
    struct { struct var_decl_expr * base; int size; } ARRAY_TYPE;
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

struct type_list * (* TTNil)();
struct type_list * (* TTCons)(struct left_type *, struct var_decl_expr *, 
                           struct type_list *);
struct enum_ele_list * (* TENil)();
struct enum_ele_list * (* TECons)(char *, struct enum_ele_list *);
struct left_type * (* TStructType)(char *);
struct left_type * (* TNewStructType)(char *, struct type_list *);
struct left_type * (* TUnionType)(char *);
struct left_type * (* TNewUnionType)(char *, struct type_list *);
struct left_type * (* TEnumType)(char *);
struct left_type * (* TNewEnumType)(char *, struct enum_ele_list *);
struct left_type * (* TIntType)();
struct left_type * (* TCharType)();
struct left_type * (* TDefinedType)(char *);
