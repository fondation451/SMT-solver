(* Type de Syntaxe abstraite *)

type file = {
  nbV : int;
  nbC : int;
  clause_l : clause list;
}

and clause = litteral list

and litteral =
  |Equal of int * int
  |Different of int * int
;;
