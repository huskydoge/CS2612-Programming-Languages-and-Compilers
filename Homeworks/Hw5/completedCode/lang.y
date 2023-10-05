%{
	// this part is copied to the beglob_itemnning of the parser 
	#include <stdio.h>
	#include "lang.h"
	#include "lexer.h"
	void yyerror(char *);
	int yylex(void);
    struct glob_item_list * root;
%}
%error-verbose
%union {
  unsigned int n;
  char * i;
  struct left_type * left_type;

  struct var_decl_expr* var_decl_exp;

  struct type_list* type_lst;
  struct enum_ele_list* enum_lst;

  struct glob_item* glob_item;
  struct glob_item_list* glob_item_lst;
  
  void * none;
}

// Terminals
%token <n> TM_NAT
%token <i> TM_IDENT
%token <none> TM_LEFT_BRACE TM_RIGHT_BRACE
%token <none> TM_LEFT_PAREN TM_RIGHT_PAREN
%token <none> TM_LEFT_SQUARE TM_RIGHT_SQUARE  // 中括号
%token <none> TM_COMMA // 逗号
%token <none> TM_DEREF // 星号
%token <none> TM_SEMICOL

%token <none> TM_STRUCT TM_INT TM_CHAR TM_UNION TM_ENUM // TYPE
%token <none> TM_TYPEDEF


// Nonterminals
%type <glob_item_lst> NT_WHOLE

%type <left_type> NT_LEFT_TYPE

%type <var_decl_exp> NT_ANNON_RIGHT_TYPE_EXPR
%type <var_decl_exp> NT_NAMED_RIGHT_TYPE_EXPR

%type <glob_item_lst> NT_GLOB_ITEM_LIST
%type <glob_item> NT_GLOB_ITEM

%type <enum_lst> NT_ENUM_ELE_LIST
%type <type_lst> NT_ARGUMENT_TYPE_LIST
%type <type_lst> NT_PACKED_ARGUEMENT_TYPE_LIST
%type <type_lst> NT_FIELD_LIST



// Priority
%right TM_COMMA
%left TM_LEFT_BRACE TM_RIGHT_BRACE
%nonassoc TM_STRUCT TM_UNION TM_ENUM TM_TYPEDEF TM_INT TM_CHAR 
%right TM_DEREF
%left  TM_LEFT_PAREN TM_RIGHT_PAREN
%left TM_LEFT_SQUARE TM_RIGHT_SQUARE
%right TM_SEMICOL
%%

NT_WHOLE:
    NT_GLOB_ITEM_LIST{
        $$ = ($1);
        root = $$;
    }

NT_GLOB_ITEM_LIST:
    NT_GLOB_ITEM {
        $$ = TGCons($1, TGNil());
    }

    | NT_GLOB_ITEM NT_GLOB_ITEM_LIST{
        $$ = TGCons($1, $2);
    }

NT_GLOB_ITEM:
  TM_STRUCT TM_IDENT TM_LEFT_BRACE NT_FIELD_LIST TM_RIGHT_BRACE TM_SEMICOL
  {
    $$ = TStructDef($2, $4);
  }
| TM_STRUCT TM_IDENT TM_SEMICOL
  {
    $$ = TStructDecl($2);
  }
| TM_UNION TM_IDENT TM_LEFT_BRACE NT_FIELD_LIST TM_RIGHT_BRACE TM_SEMICOL
  {
    $$ = TUnionDef($2, $4);
  }
| TM_UNION TM_IDENT TM_SEMICOL
  {
    $$ = TUnionDecl($2);
  }
|   TM_ENUM TM_IDENT TM_LEFT_BRACE NT_ENUM_ELE_LIST TM_RIGHT_BRACE TM_SEMICOL
  {
    $$ = TEnumDef($2, $4);
  }
| TM_ENUM TM_IDENT TM_SEMICOL
  {
    $$ = TEnumDecl($2);
  }
| TM_TYPEDEF NT_LEFT_TYPE NT_NAMED_RIGHT_TYPE_EXPR TM_SEMICOL
  {
    $$ = TTypeDef($2, $3);
  }
| NT_LEFT_TYPE NT_NAMED_RIGHT_TYPE_EXPR TM_SEMICOL
  {
    $$ = TVarDef($1, $2);
  }

NT_ENUM_ELE_LIST:
  TM_IDENT
  {
    $$ = TECons($1, TENil());
  }
| TM_IDENT TM_COMMA NT_ENUM_ELE_LIST
  {
    $$ = TECons($1, $3);
  }


NT_LEFT_TYPE:
  TM_IDENT {
    $$ = TDefinedType($1);
    }
| TM_STRUCT TM_IDENT TM_LEFT_BRACE NT_FIELD_LIST TM_RIGHT_BRACE
  {
    $$ = TNewStructType($2, $4);
  }
| TM_STRUCT TM_LEFT_BRACE NT_FIELD_LIST TM_RIGHT_BRACE
  {
    $$ = TNewStructType(NULL, $3);
  }
| TM_STRUCT TM_IDENT
  {
    $$ = TStructType($2);
  }
| TM_UNION TM_IDENT TM_LEFT_BRACE NT_FIELD_LIST TM_RIGHT_BRACE
  {
    $$ = TNewUnionType($2, $4);
  }
| TM_UNION TM_LEFT_BRACE NT_FIELD_LIST TM_RIGHT_BRACE
  {
    $$ = TNewUnionType(NULL, $3);
  }
| TM_UNION TM_IDENT
  {
    $$ = TUnionType($2);
  }
| TM_ENUM TM_IDENT TM_LEFT_BRACE NT_ENUM_ELE_LIST TM_RIGHT_BRACE
  {
    $$ = TNewEnumType($2, $4);
  }
| TM_ENUM TM_LEFT_BRACE NT_ENUM_ELE_LIST TM_RIGHT_BRACE
  {
    $$ = TNewEnumType(NULL, $3);
  }
| TM_ENUM TM_IDENT
  {
    $$ = TEnumType($2);
  }
| TM_INT
  {
    $$ = TIntType();
  }
| TM_CHAR
  {
    $$ = TCharType();
  }
;


NT_NAMED_RIGHT_TYPE_EXPR:
TM_DEREF NT_NAMED_RIGHT_TYPE_EXPR // * expr
  {
    $$ = TPtrType($2);
  }
| TM_LEFT_PAREN NT_NAMED_RIGHT_TYPE_EXPR TM_RIGHT_PAREN // 考虑括号优先级, (expr)
  {
    $$ = $2;
}
| TM_IDENT
  {
    $$ = TOrigType($1);
  }
| NT_NAMED_RIGHT_TYPE_EXPR TM_LEFT_SQUARE TM_NAT TM_RIGHT_SQUARE
  {
    $$ = TArrayType($1, $3);
  }
| NT_NAMED_RIGHT_TYPE_EXPR NT_PACKED_ARGUEMENT_TYPE_LIST
  {
    $$ = TFuncType($1, $2);
  }
;

NT_ANNON_RIGHT_TYPE_EXPR:
TM_LEFT_PAREN NT_ANNON_RIGHT_TYPE_EXPR TM_RIGHT_PAREN // 括号优先级
  {
    $$ = $2
  }
| TM_DEREF NT_ANNON_RIGHT_TYPE_EXPR
  {
    $$ = TPtrType($2);
  }
| TM_DEREF
  {
    $$ = TPtrType(TOrigType(""));
  }
| NT_ANNON_RIGHT_TYPE_EXPR TM_LEFT_SQUARE TM_NAT TM_RIGHT_SQUARE
  {
    $$ = TArrayType($1, $3);
  }
| TM_LEFT_SQUARE TM_NAT TM_RIGHT_SQUARE
  {
    $$ = TArrayType(TOrigType(""), $2);
  }
| NT_ANNON_RIGHT_TYPE_EXPR NT_PACKED_ARGUEMENT_TYPE_LIST
  {
    $$ = TFuncType($1, $2);
  }
| NT_PACKED_ARGUEMENT_TYPE_LIST
  {
    $$ = TFuncType(TOrigType(""), $1);
  }
;


NT_FIELD_LIST:
    {$$ = TTNil();}
| NT_LEFT_TYPE NT_NAMED_RIGHT_TYPE_EXPR TM_SEMICOL NT_FIELD_LIST
  {
    $$ = TTCons($1, $2, $4);
  }
;


NT_PACKED_ARGUEMENT_TYPE_LIST:
    TM_LEFT_PAREN NT_ARGUMENT_TYPE_LIST TM_RIGHT_PAREN
    {
        $$ = $2;
    }
;

NT_ARGUMENT_TYPE_LIST:
    {$$ = TTNil();}
|  NT_LEFT_TYPE NT_ANNON_RIGHT_TYPE_EXPR TM_COMMA NT_ARGUMENT_TYPE_LIST
  {
    $$ = TTCons($1, $2, $4);
  }
|  NT_LEFT_TYPE TM_COMMA NT_ARGUMENT_TYPE_LIST
  {
    $$ = TTCons($1, TOrigType(""), $3);
  }
|  NT_LEFT_TYPE NT_ANNON_RIGHT_TYPE_EXPR
  {
    $$ = TTCons($1, $2, TTNil());
  }
|  NT_LEFT_TYPE
  {
    $$ = TTCons($1, TOrigType(""), TTNil());
  }
;  
%%

void yyerror(char* s)
{
    fprintf(stderr , "%s\n",s);
    fprintf(stderr , "line %d\n",yylineno);
    fprintf(stderr , "token %s\n",yytext);
    fprintf(stderr , "token %s\n",yytext);
    fprintf(stderr , "token %s\n",yytext);
    fprintf(stderr , "token type %d\n",yylex());
    fprintf(stderr , "token type %d\n",yylex());
    fprintf(stderr , "token type %d\n",yylex());
}
