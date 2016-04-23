(* Type de Syntaxe abstraite *)

type ast_file = {
  nbV : int;
  nbC : int;
  clause_l : ast_clause list;
}

and ast_clause = ast_litteral list

and ast_litteral =
  |Equal of int * int
  |Different of int * int
;;










































