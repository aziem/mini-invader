{ (* Header *)
  
open Lexing
open Parser

(* Association list of keywords *)
let keywords = [
  ("emp", EMPTY);
  ("dispose", DISPOSE);
  ("lseg", LISTSEG);
  ("new", NEW);
  ("if", IF);
  ("else", ELSE);
  ("while", WHILE);
  ("NULL", NULL);
  ("goto", GOTO);
  ("true", TRUE);
  ("false",FALSE);	
  ("return", RETURN);
]
  


}

(* Regular expressions *)

let newline = ('\010' | '\013' | "\013\010")
let blank = [' ' '\009' '\012']
let letter = ['A'-'Z' '_' 'a'-'z']
let digit = ['0'-'9']
let alphanum = digit | letter
let ident = letter alphanum*

(* Entry points *)

rule token = parse
  | newline { token lexbuf }
  | blank+ { token lexbuf }
  | "/*" { comment lexbuf; token lexbuf }
  | "'" { PRIME }  (* !!! Remove this *)
  | "^" { HAT } (* !!! Remove this *)
  | "|->" { POINTSTO }
  | "|" { DELIM }
  | "," { COMMA }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "[" { LBRACKET }
  | "]" { RBRACKET }
  | ";" { SEMI }
  | "==" { EQUALEQUAL }
  | "=" { EQUAL }
  | "!=" { UNEQUAL }
  | "/\\" { CONJ }
  | "*" { STAR }
  | "{" { LBRACE }
  | "}" { RBRACE }
  | ['0'-'9']+ {NUM(int_of_string (Lexing.lexeme lexbuf)) }
  | ident { let s = Lexing.lexeme lexbuf in
              try List.assoc s keywords
              with Not_found -> IDENT(s) }
  | eof { EOF }
  | _ { raise(Error.Illegal_character) }

and comment = parse
    "*/" { () }
  | eof { raise(Error.Unterminated_comment) }
  | _ { comment lexbuf }

{ (* Trailer *)
}
