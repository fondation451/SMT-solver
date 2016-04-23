(* Type de Syntaxe abstraite *)

type ast_file = {
  nbV : int;
  nbC : int;
  clause_l : clause list;
}

and ast_clause = litteral list

and ast_litteral =
  |Equal of int * int
  |Different of int * int
;;
