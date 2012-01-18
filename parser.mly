%{ (* Header *)

open Global
open Parsetree

%} /* declarations */

/* tokens */

%token COMMA
%token CONJ
%token DELIM
%token DISPOSE
%token ELSE
%token EMPTY
%token EOF
%token EQUAL
%token EQUALEQUAL
%token HAT
%token <string> IDENT
%token IF
%token LBRACE
%token LBRACKET
%token LISTSEG
%token LPAREN
%token NEW
%token NULL
%token POINTSTO
%token PRIME
%token RBRACE
%token RBRACKET
%token RETURN
%token RPAREN
%token SEMI
%token STAR
%token UNEQUAL
%token WHILE
%token GOTO
%token <int> NUM
%token TRUE
%token FALSE
%token RETURN

/* precedences (increasing) and associativities for expressions */

%nonassoc below_ELSE
%nonassoc ELSE
%left STAR CONJ

/* entry points */

%start program
%type <Parsetree.program> program

%start assertion
%type <Parsetree.assertion> assertion


%% /* rules */

program:
  | /* empty */
      { [] }
  | fun_decl program
      { $1::$2 }
;

fun_decl:
  | funident LPAREN formal_params RPAREN LBRACE statements RBRACE
      { FunDecl($1, $3, $6) }
;

formal_params:
  | /* empty */
      { [] }
  | ident
      { [$1] }
  | ident COMMA formal_params
      { $1::$3 }
;

actual_params:
  | /* empty */
      { [] }
  | expression
      { [$1] }
  | expression COMMA actual_params
      { $1::$3 }
;

statements:
  | /* empty */
      { [] }
  | statement statements
      { $1::$2 }
;

funident:
  | IDENT
      { $1 }
;

ident:
  /* !!! Remove this : make different types for program and assertions*/
  | IDENT PRIME
      { PrimedVar($1) }
  | IDENT
      { Vari($1) }
;

expression:
  | ident
      { Identifier($1) }
  | NULL
      { Nil }
;

condition:
  | expression EQUALEQUAL expression
      { IfEqual($1, $3) }
  | expression UNEQUAL expression
      { IfUnequal($1, $3) }
  | TRUE 
      { STrue }
  | FALSE 
      { SFalse }
  | STAR 
      { NondetChoice }
;

statement:
  | SEMI
      { StmtSkip }
  | LBRACE statements RBRACE
      { StmtBlock($2) }
  | ident EQUAL expression SEMI
      { StmtAssign($1, $3) }
  | ident EQUAL LBRACKET ident RBRACKET SEMI
      { StmtLookup($1, $4) }
  | LBRACKET ident RBRACKET EQUAL expression SEMI
      { StmtMemAssign($2, $5) }
  | DISPOSE ident SEMI
      { StmtDispose($2) }
  | NEW ident SEMI
      { StmtNew($2) }
  | IF LPAREN condition RPAREN statement %prec below_ELSE
      { StmtIf($3, $5, StmtBlock([])) }
  | IF LPAREN condition RPAREN statement ELSE statement
      { StmtIf($3, $5, $7) }
  | WHILE LPAREN condition RPAREN statement
      { StmtWhile($3, $5) }
  | GOTO num
      { StmtGoto($2) } 
  | RETURN expression SEMI
      { StmtReturn($2) }
;

num:
  | NUM {$1}
;

assertion:
  | pure_preds DELIM space_preds
      { Assertion($1, $3) }
;

space_preds:
  | /* empty */
      { [] }
  | space_pred
      { [$1] }
  | space_pred STAR space_preds
      { $1::$3 }
;

pure_preds:
  | /* empty */
      { [] }
  | pure_pred
      { [$1] }
  | pure_pred CONJ pure_preds
      { $1::$3 }
;

space_pred:
  | EMPTY
      { SpacePredEmpty }
  | ident POINTSTO expression
      { SpacePredPointsTo($1, $3) }
  | LISTSEG LPAREN expression COMMA expression RPAREN
      { SpacePredListseg($3, $5) }
;

pure_pred:
  | expression EQUAL expression
      { PurePredEquality($1, $3) }
;

%% (* Trailer *)
