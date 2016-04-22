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

module PUF = Persistent_union_find

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

let empty_memo = {code = Tmap.empty;
                  next_code = 0;
                  congruence = PUF.create 0}

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

let rec close_by_congruence memo =
  let is_congr t1 t2 =
    match t1,t2 with
    | Const s1, Const s2 -> s1 = s2
    | Fun (f1,arg1), Fun (f2,arg2) ->
        f1 = f2 && List.for_all (fun (tt1,tt2) -> 
                                   let tt1_code,_ = get_code_term memo tt1
                                   and tt2_code,_ = get_code_term memo tt2 in
                                   PUF.find memo.congruence tt1_code = PUF.find memo.congruence tt2_code)
                                (List.combine arg1 arg2)
    | _,_ -> false
  in
  let new_rel = Tmap.fold (fun t1 c1 rel1 -> 
                             Tmap.fold (fun t2 c2 rel2 -> if is_congr t1 t2 
                                                          then PUF.union rel2 c1 c2 
                                                          else rel2) memo.code rel1)
                          memo.code memo.congruence
  in
  if memo.congruence = new_rel then new_rel
  else close_by_congruence (set_congruence memo new_rel)

let rec gen_congruence memo l_eq =
  match l_eq with
  | [] -> set_congruence memo (close_by_congruence memo)
  | (x,y)::ls ->
      let x_code,memo' = get_code_term memo x in
      let y_code,memo'' = get_code_term memo' y in
      if PUF.find memo.congruence x_code <> PUF.find memo.congruence y_code
      then gen_congruence (set_congruence memo''
                             (PUF.union memo.congruence x_code y_code)) 
                          ls
      else gen_congruence memo'' ls

let is_satisfiable_mod_theory memo l =
  let l_eq,l_not_eq = split_eq l in
  let memo_res = gen_congruence memo l_eq in
  List.for_all (fun (x,y) ->
                  let x_code,_ = get_code_term memo_res x
                  and y_code,_ = get_code_term memo_res y in
                  PUF.find memo_res.congruence x_code <> PUF.find memo_res.congruence y_code)
               l_not_eq

let () =
  let ex = [Eq (Const "x",Const "y")] in
  print_endline (string_of_bool (is_satisfiable_mod_theory empty_memo ex))
