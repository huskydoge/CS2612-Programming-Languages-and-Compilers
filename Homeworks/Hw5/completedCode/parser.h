/* A Bison parser, made by GNU Bison 2.3.  */

/* Skeleton interface for Bison's Yacc-like parsers in C

   Copyright (C) 1984, 1989, 1990, 2000, 2001, 2002, 2003, 2004, 2005, 2006
   Free Software Foundation, Inc.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2, or (at your option)
   any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin Street, Fifth Floor,
   Boston, MA 02110-1301, USA.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* Tokens.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
   /* Put the tokens into the symbol table, so that GDB and other debuggers
      know about them.  */
   enum yytokentype {
     TM_NAT = 258,
     TM_IDENT = 259,
     TM_LEFT_BRACE = 260,
     TM_RIGHT_BRACE = 261,
     TM_LEFT_PAREN = 262,
     TM_RIGHT_PAREN = 263,
     TM_LEFT_SQUARE = 264,
     TM_RIGHT_SQUARE = 265,
     TM_COMMA = 266,
     TM_DEREF = 267,
     TM_SEMICOL = 268,
     TM_STRUCT = 269,
     TM_INT = 270,
     TM_CHAR = 271,
     TM_UNION = 272,
     TM_ENUM = 273,
     TM_TYPEDEF = 274
   };
#endif
/* Tokens.  */
#define TM_NAT 258
#define TM_IDENT 259
#define TM_LEFT_BRACE 260
#define TM_RIGHT_BRACE 261
#define TM_LEFT_PAREN 262
#define TM_RIGHT_PAREN 263
#define TM_LEFT_SQUARE 264
#define TM_RIGHT_SQUARE 265
#define TM_COMMA 266
#define TM_DEREF 267
#define TM_SEMICOL 268
#define TM_STRUCT 269
#define TM_INT 270
#define TM_CHAR 271
#define TM_UNION 272
#define TM_ENUM 273
#define TM_TYPEDEF 274




#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE
#line 11 "lang.y"
{
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
/* Line 1529 of yacc.c.  */
#line 103 "parser.h"
	YYSTYPE;
# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
# define YYSTYPE_IS_TRIVIAL 1
#endif

extern YYSTYPE yylval;

