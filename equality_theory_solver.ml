type term = int;;

type atomic_formula =
  |Eq of term * term
  |Not_eq of term * term
;;

module Tmap =
  Map.Make(struct
    type t = term
  let compare = compare
  end)
;;

module PUF = Persistent_union_find;;

type memo = {
  code : int Tmap.t;
  next_code : int;
  congruence : Persistent_union_find.t
};;

let set_code memo code = {
  code = code;
  next_code = memo.next_code;
  congruence = memo.congruence
};;

let set_next_code memo next_code = {
  code = memo.code;
  next_code = next_code;
  congruence = memo.congruence
};;

let set_congruence memo congruence = {
  code = memo.code;
  next_code = memo.next_code;
  congruence = congruence
};;

let empty_memo = {
  code = Tmap.empty;
  next_code = 0;
  congruence = PUF.create 0
};;

let split_eq l =
  let rec aux l out_eq out_not_eq =
    match l with
    |[] -> out_eq, out_not_eq
    |t::ls -> begin
      match t with
      |Eq (x,y) -> aux ls ((x, y)::out_eq) out_not_eq
      |Not_eq (x,y) -> aux ls out_eq ((x, y)::out_not_eq)
    end
  in
  aux l [] []
;;

(* let insert_term memo t =
  set_code memo (Tset.add t memo.code)
;; *)

let get_code_term memo t =
  if Tmap.mem t memo.code then
    Tmap.find t memo.code, memo
  else 
    let new_code = Tmap.add t memo.next_code memo.code in
    memo.next_code, set_code (set_next_code memo (memo.next_code + 1)) new_code
;;

(* let adapt_size_congruence memo l =
  let memo' = List.fold_left (fun m t -> insert_term m t) memo l in
  printf "taille = %d\n" ((Tset.cardinal memo'.code + 1) - PUF.length memo.congruence);
  set_congruence memo' (PUF.expand memo.congruence ((Tset.cardinal memo'.code + 1) - PUF.length memo.congruence))
;; *)

let adapt_size_congruence memo l =
  let rec gen_code m t = snd (get_code_term m t) in
  let memo' = List.fold_left gen_code memo l in
  set_congruence memo' (PUF.expand memo.congruence (memo'.next_code - PUF.length memo.congruence))
;;

let rec gen_congruence memo l_eq =
  match l_eq with
  |[] -> memo
  |(x, y)::ls ->
    let x_code,memo' = get_code_term memo x in
    let y_code,memo'' = get_code_term memo' y in
    if PUF.find memo.congruence x_code <> PUF.find memo.congruence y_code then
      gen_congruence (set_congruence memo'' (PUF.union memo.congruence x_code y_code)) ls
    else
      gen_congruence memo'' ls
;;

let rec find_conflict memo ln =
  match ln with
  |[] -> None
  |(x, y)::tail ->
    let x_code,_ = get_code_term memo x
    and y_code,_ = get_code_term memo y in
    if PUF.find memo.congruence x_code = PUF.find memo.congruence y_code then
      Some((x, y))
    else
      find_conflict memo tail
;;

let find_equality_of_conflict memo rep l_eq =
  let rec aux l out =
    match l with
    |[] -> out
    |(x, y)::tail ->
      let x_code,_ = get_code_term memo x in
      if PUF.find memo.congruence x_code = rep then
        aux tail ((Not_eq(x, y))::out)
      else
        aux tail out
  in
  aux l_eq []
;;

let is_satisfiable_mod_theory memo l =
  let l_eq, l_not_eq = split_eq l in
  let (l_eq_l, l_eq_r),(l_not_eq_l, l_not_eq_r) = List.split l_eq, List.split l_not_eq in
  let memo_adapted = adapt_size_congruence memo (l_eq_l@l_eq_r@l_not_eq_l@l_not_eq_r) in
  let memo_res = gen_congruence memo_adapted l_eq in
  match find_conflict memo_res l_not_eq with
  |None -> true, memo_res, []
  |Some((x, y)) ->
    let x_code,_ = get_code_term memo_res x in
    let l_eq_conflict = find_equality_of_conflict memo_res (PUF.find memo_res.congruence x_code) l_eq in
    false, memo_res, ((Eq(x, y))::l_eq_conflict)
;;


