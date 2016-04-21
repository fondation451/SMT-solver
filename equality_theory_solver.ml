type term =
  | Const of string
  | Fun of string * term list

type atomic_formula =
  | Eq of term * term
  | Not_eq of term * term

module Ordered_term = struct
  type t = term
  let compare = compare
end

module Tmap = Map.Make(Ordered_term)

type memo = {code : int Tmap.t; 
             next_code : int;
             congruence : Persistent_union_find.t}

let set_code memo code = {code = code;
                          next_code = memo.next_code;
                          congruence = memo.congruence}

let set_next_code memo next_code = {code = memo.code;
                                    next_code = next_code;
                                    congruence = memo.congruence}

let set_congruence memo congruence = {code = memo.code;
                                      next_code = memo.next_code;
                                      congruence = congruence}

let rec split_eq l =
  match l with
  | [] -> [],[]
  | t::ls ->
      let l_eq,l_not_eq = split_eq ls in
      begin match t with
      | Eq (x,y) -> (x,y)::l_eq,l_not_eq
      | Not_eq (x,y) -> l_eq,(x,y)::l_not_eq
      end
      
let get_code_term memo t =
  if Tmap.mem t memo.code then Tmap.find t memo.code,memo
  else 
    let new_code = Tmap.add t memo.next_code memo.code in
    memo.next_code, set_code (set_next_code memo (memo.next_code + 1)) 
                             new_code

let rec gen_congruence memo l_eq =
  match l_eq with
  | [] -> memo
  | (x,y)::ls ->
      let x_code,memo' = get_code_term memo x in
      let y_code,memo'' = get_code_term memo' y in
      if Persistent_union_find.find memo.congruence x_code <> Persistent_union_find.find memo.congruence y_code
      then gen_congruence (set_congruence memo''
                             (Persistent_union_find.union memo.congruence x_code y_code)) 
                          ls
      else gen_congruence memo'' ls

let is_satisfiable_mod_theory memo l =
  let l_eq,l_net_eq = split_eq l in
  let rel_congruence = gen_congruence memo l_eq in
  assert false
