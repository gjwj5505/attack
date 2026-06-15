%{
open Syntax

module E = Exp
module S = Stmt
%}

%token <int> INT_LITERAL
%token <string> ID
%token KW_INT KW_MAIN
%token KW_IF KW_ELSE KW_WHILE KW_RETURN
%token ASSIGN
%token EQ NE LT LE GT GE
%token PLUS MINUS TIMES DIV MOD
%token LPAREN RPAREN LBRACE RBRACE
%token SEMI
%token EOF

%start <Syntax.program> prog
%type <Stmt.codeblock> codeblock
%type <Stmt.t> stmt
%type <lval> lval
%type <Exp.t> expr equality relational additive multiplicative unary primary
%%

prog:
  | KW_INT; KW_MAIN; LPAREN; RPAREN; body = codeblock; EOF
      {
        {
          main =
            {
              ret_type = Typ.Int;
              name = "main";
              params = [];
              body;
            };
        }
      }

codeblock:
  | LBRACE; ss = nonempty_list(stmt); RBRACE { ss }

stmt:
  | KW_INT; x = ID; ASSIGN; e = expr; SEMI
      { S.Decl ({ typ = Typ.Int; name = x }, e) }
  | lv = lval; ASSIGN; e = expr; SEMI
      { S.Assign (lv, e) }
  | KW_IF; LPAREN; cond = expr; RPAREN; tb = codeblock; KW_ELSE; fb = codeblock
      { S.If (cond, tb, fb) }
  | KW_WHILE; LPAREN; cond = expr; RPAREN; body = codeblock
      { S.While (cond, body) }
  | KW_RETURN; e = expr; SEMI
      { S.Return e }

lval:
  | x = ID { LVar x }

expr:
  | e = equality { e }

equality:
  | e = relational { e }
  | e1 = equality; EQ; e2 = relational { E.Bop (E.Eq, e1, e2) }
  | e1 = equality; NE; e2 = relational { E.Bop (E.Ne, e1, e2) }

relational:
  | e = additive { e }
  | e1 = relational; LT; e2 = additive { E.Bop (E.Lt, e1, e2) }
  | e1 = relational; LE; e2 = additive { E.Bop (E.Le, e1, e2) }
  | e1 = relational; GT; e2 = additive { E.Bop (E.Gt, e1, e2) }
  | e1 = relational; GE; e2 = additive { E.Bop (E.Ge, e1, e2) }

additive:
  | e = multiplicative { e }
  | e1 = additive; PLUS; e2 = multiplicative { E.Bop (E.Plus, e1, e2) }
  | e1 = additive; MINUS; e2 = multiplicative { E.Bop (E.Minus, e1, e2) }

multiplicative:
  | e = unary { e }
  | e1 = multiplicative; TIMES; e2 = unary { E.Bop (E.Times, e1, e2) }
  | e1 = multiplicative; DIV; e2 = unary { E.Bop (E.Div, e1, e2) }
  | e1 = multiplicative; MOD; e2 = unary { E.Bop (E.Mod, e1, e2) }

unary:
  | e = primary { e }
  | MINUS; e = unary { E.Uop (E.Uminus, e) }

primary:
  | n = INT_LITERAL { E.Int n }
  | lv = lval { E.Lval lv }
  | LPAREN; e = expr; RPAREN { e }
