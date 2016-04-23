open Ast;;
open Parser;;
open Lexer;;
open Smt;;
open Format;;
open Lexing;;

let input_file = ref "";;

let usage = "usage: smt_solver file.cnf";;

let set_file f s = f := s;;


let () =
  Arg.parse [] (set_file input_file) usage;
  
  if !input_file = "" then begin
    eprintf "No input file\n@?";
    exit 2
  end;
  
  let f = open_in !input_file in
  let buf = Lexing.from_channel f in
  
  try
    let formula = Parser.file Lexer.next_tokens buf in
    close_in f;
            
    let satisfiability = Smt.smt_solver formula in
    if satisfiability then begin
      print_endline "SAT";
      exit 0
    end
    else begin
      print_endline "UNSAT";
      exit 1
    end
  with
    |Lexical_error(str) ->
      eprintf "Erreur Lexical@.";
      Printf.printf "%s\n" str;
      exit 2
    |Parser.Error ->
      eprintf "Erreur syntaxique@.";
      exit 2
    |_ -> exit 3
;;



































