{
open Lexing
open Parser

exception SyntaxError of string

let keywords =
  let tbl : (string, token) Hashtbl.t = Hashtbl.create 10 in
  let add_to_tbl (id, tok) = Hashtbl.add tbl id tok in
  List.iter add_to_tbl
    [
      ("int", KW_INT);
      ("main", KW_MAIN);
      ("if", KW_IF);
      ("else", KW_ELSE);
      ("while", KW_WHILE);
      ("return", KW_RETURN);
    ];
  tbl
}

let blank = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let digit = ['0'-'9']
let int = digit+

rule read =
  parse
  | blank      { read lexbuf }
  | newline    { new_line lexbuf; read lexbuf }
  | "//"       { line_comment lexbuf; read lexbuf }
  | "/*"       { block_comment lexbuf; read lexbuf }
  | int as n   { INT_LITERAL (int_of_string n) }
  | id as s    { match Hashtbl.find_opt keywords s with Some tok -> tok | None -> ID s }
  | "=="       { EQ }
  | "!="       { NE }
  | "<="       { LE }
  | ">="       { GE }
  | '='        { ASSIGN }
  | '<'        { LT }
  | '>'        { GT }
  | '+'        { PLUS }
  | '*'        { TIMES }
  | '/'        { DIV }
  | '%'        { MOD }
  | '-'        { MINUS }
  | '('        { LPAREN }
  | ')'        { RPAREN }
  | '{'        { LBRACE }
  | '}'        { RBRACE }
  | ';'        { SEMI }
  | eof        { EOF }
  | _          { raise (SyntaxError ("Unexpected char: " ^ lexeme lexbuf)) }

and line_comment =
  parse
  | newline { new_line lexbuf }
  | eof     { () }
  | _       { line_comment lexbuf }

and block_comment =
  parse
  | "*/"    { () }
  | newline { new_line lexbuf; block_comment lexbuf }
  | eof     { raise (SyntaxError "Unclosed block comment") }
  | _       { block_comment lexbuf }
