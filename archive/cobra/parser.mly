%{
open Exprs

let full_span() = (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())
let tok_span(start, endtok) = (Parsing.rhs_start_pos start, Parsing.rhs_end_pos endtok)
%}

%token <int64> NUM
%token <string> ID
%token ADD1 SUB1 LPAREN RPAREN LET IN EQUAL COMMA PLUS MINUS TIMES IF COLON ELSECOLON EOF PRINT PRINTSTACK TRUE FALSE ISBOOL ISNUM EQEQ LESS GREATER LESSEQ GREATEREQ AND OR NOT

%left PLUS MINUS TIMES GREATER LESS GREATEREQ LESSEQ EQEQ AND OR


%type <Exprs.sourcespan Exprs.expr> program

%start program

%%

const :
  | NUM { ENumber($1, full_span()) }
  | TRUE { EBool(true, full_span()) }
  | FALSE { EBool(false, full_span()) }

prim1 :
  | ADD1 { Add1 }
  | SUB1 { Sub1 }
  | NOT { Not }
  | PRINT { Print }
  | ISBOOL { IsBool }
  | ISNUM { IsNum }
  | PRINTSTACK { PrintStack }

binds :
  | ID EQUAL expr { [($1, $3, full_span())] }
  | ID EQUAL expr COMMA binds { ($1, $3, tok_span(1, 3))::$5 }

binop_expr :
  | prim1 LPAREN expr RPAREN { EPrim1($1, $3, full_span()) }
  | LPAREN expr RPAREN { $2 }
  | binop_expr PLUS binop_expr { EPrim2(Plus, $1, $3, full_span()) }
  | binop_expr MINUS binop_expr { EPrim2(Minus, $1, $3, full_span()) }
  | binop_expr TIMES binop_expr { EPrim2(Times, $1, $3, full_span()) }
  | binop_expr AND binop_expr { EPrim2(And, $1, $3, full_span()) }
  | binop_expr OR binop_expr { EPrim2(Or, $1, $3, full_span()) }
  | binop_expr GREATER binop_expr { EPrim2(Greater, $1, $3, full_span()) }
  | binop_expr GREATEREQ binop_expr { EPrim2(GreaterEq, $1, $3, full_span()) }
  | binop_expr LESS binop_expr { EPrim2(Less, $1, $3, full_span()) }
  | binop_expr LESSEQ binop_expr { EPrim2(LessEq, $1, $3, full_span()) }
  | binop_expr EQEQ binop_expr { EPrim2(Eq, $1, $3, full_span()) }
  | const { $1 }
  | ID { EId($1, full_span()) }

expr :
  | LET binds IN expr { ELet($2, $4, full_span()) }
  | IF expr COLON expr ELSECOLON expr { EIf($2, $4, $6, full_span()) }
  | binop_expr { $1 }

program :
  | expr EOF { $1 }

%%
