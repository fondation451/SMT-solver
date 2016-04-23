{
  open Ma_spec
  open Mon_parser
  open Lexing
  
  exception Lexical_error of string;;
}

let digit = ['0'-'9']
let integer = '0' | ['1'-'9'] digit*

rule next_tokens = parse
  |"\n" {NEXT}
  |[' ' '\t']+ {next_tokens lexbuf} (* Gestion des blancs *)
  |integer as str_n {VAR(int_of_string str_n)}
  |"p" {HEADER}
  |"cnf" {CNF}
  |"=" {EQUAL}
  |"<>" {DIFFERENT}
  |"c" {comment_line lexbuf}
  |eof {EOF}
  |_ {raise (Lexical_error "Caractere inattendu !")}

and comment_line = parse
  |"\n" {next_tokens lexbuf}
  |_ {comment_line lexbuf}
  |eof {EOF}
  















































