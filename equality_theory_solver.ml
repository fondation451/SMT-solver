type term =
  | Const of string
  | Fun of string * term list

type atomic_formula =
  | Eq of term * term
  | Not_eq of term * term

let split_eq l =
  match l with
  | [] -> [],[]
  | t::ls ->
      let l_eq,l_not_eq = split_eq ls in
      begin match t with
      | Eq (x,y) -> (x,y)::l_eq,l_not_eq
      | Not_eq (x,y) -> l_eq,(x,y)::l_not_eq
      end
      
