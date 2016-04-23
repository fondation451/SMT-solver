open Printf;;
open Scanf;;
open Ast;;

(* Type definition for SAT solver *)

type litteral = {id : int; negation : bool};;

type clause = litteral list;;

type cnf = clause list;;

type model_var = {var : litteral; inferred : bool};;

type model = model_var list;;

exception Unit_clause_found of litteral * clause;;

exception Undefined_litteral_found of litteral;;

exception Undefined_behaviour;;

(**************************)
(* Type definition for theory satisfiability *)
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

(**************************)
(* Quick research of antecedent *)
module AnteMap =
  Map.Make(struct
    type t = int
    let compare = compare
  end)
;;

(* Quick research of level *)
module LevelMap =
  Map.Make(struct
    type t = int
    let compare = compare
  end)
;;

(**************************)
(* Printing functions *)

let print_litteral l =
  if l.negation then
    printf "n";
  printf "%d" l.id
;;

let rec print_clause cl =
  match cl with
  |[] -> ()
  |head::[] -> print_litteral head
  |head::tail ->
    print_litteral head;
    printf " \\/ ";
    print_clause tail
;;

let rec print_CNF f =
  match f with
  |[] -> ()
  |head::[] ->
    printf "(";
    print_clause head;
    printf ")"
  |head::tail ->
    printf "(";
    print_clause head;
    printf ") /\\ ";
    print_CNF tail
;;

let print_model m level =
  let rec aux m =
    match m with
    |[] -> ()
    |l::ls ->
      printf "(";
      if l.var.negation = true then print_string "n";
      print_int l.var.id;
      if l.inferred = false then print_string "@";
      printf ", %d) " (LevelMap.find l.var.id level);
      aux ls
  in
  aux m;
  print_newline ()
;;

let rec print_eq l =
  match l with
  |[] -> printf "\n"
  |(Eq(x, y))::tail -> printf "%d = %d | " x y; print_eq tail
  |(Not_eq(x, y))::tail -> printf "%d <> %d | " x y; print_eq tail
;;

(**************************)
(* 3SAT CNF reader *)
let read_SAT str =
  let ci = open_in str in
  let header = ref (input_line ci) in
  while (!header).[0] = 'c' do
    header := input_line ci
  done;
  let nb_var, nb_cl = sscanf (!header) "p cnf %d %d " (fun x y -> x, y) in
  let out = ref [] in
  for i = 1 to nb_cl do
    let cl = ref [] in
    let l = ref (fscanf ci " %d " (fun x -> x)) in
    while !l <> 0 do
      cl := ({id = abs !l; negation = !l < 0})::(!cl);
      l := fscanf ci " %d " (fun x -> x)
    done;
    out := (!cl)::(!out)
  done;
  close_in ci;
  !out
;;

(* Preprocessing of AST  *)
let order_ast f =
  let rec aux c out =
    match c with
    |[] -> out
    |head::tail -> begin
      match head with
      |Equal(x, y) -> aux tail ((if x < y then Eq(x, y) else Eq(y, x))::out)
      |Different(x, y) -> aux tail ((if x < y then Not_eq(x, y) else Not_eq(y, x))::out)
    end
  in
  List.map (fun c -> aux c []) f.clause_l
;;

let rec tab_find tab x i =
  if tab.(i) = x then
    i
  else
    tab_find tab x (i+1)
;;

let rec theory_to_CNF c tab_id out = 
  match c with
  |[] -> out
  |head::tail -> begin
    match head with
    |Eq(x, y) ->
      let id = tab_find tab_id (x, y) 0 in
      theory_to_CNF tail tab_id ({id = id; negation = false}::out)
    |Not_eq(x, y) ->
      let id = tab_find tab_id (x, y) 0 in
      theory_to_CNF tail tab_id ({id = id; negation = true}::out)
  end
;;

let to_CNF f =
  let rec list_of_litterals c out =
    match c with
    |[] -> out
    |head::tail -> begin
      match head with
      |Eq(x, y) |Not_eq(x, y) ->
        if List.mem (x, y) out then
          list_of_litterals tail out
        else
          list_of_litterals tail ((x, y)::out)
    end
  in
  let tab_id = Array.of_list (List.fold_left (fun out c -> list_of_litterals c out) [] f) in
  (List.map (fun c -> theory_to_CNF c tab_id []) f, tab_id)
;;

let model_to_theory m tab_id =
  let rec aux m out =
    match m with
    |[] -> out
    |head::tail ->
      let x, y = tab_id.(head.var.id) in
      if head.var.negation then
        aux tail (Not_eq(x, y)::out)
      else
        aux tail (Eq(x, y)::out)
  in
  aux m []
;;

(**************************)
(* SAT solver : rules and functions *)
let nb_var_CNF f =
  let rec aux f out =
    match f with
    |[] -> out
    |head::tail ->
      let tmp = List.hd (List.sort (fun x y -> compare y.id x.id) head) in
      if tmp.id > out then
        aux tail tmp.id
      else
        aux tail out
  in
  aux f (-1)
;;

let negate_litteral l =
  {id = l.id; negation = not l.negation}
;;

let rec negate_clause c =
  match c with
  |[] -> []
  |l::ls -> [negate_litteral l]::(negate_clause ls)
;;

let rec is_defined_in_model lit m =
  match m with
  |[] -> false
  |l::ls ->
    if l.var.id = lit.id then
      true
    else is_defined_in_model lit ls
;;

let rec value_of_litteral_in_model l m =
  match m with
  |[] -> None
  |lm::ls ->
    if lm.var.id = l.id && lm.var.negation = l.negation then
      Some true
    else if lm.var.id = l.id then
      Some false
    else value_of_litteral_in_model l ls
;;

let satisfied_by_model f m =
  let litteral_true l =
    match value_of_litteral_in_model l m with
    |Some true -> true
    |_ -> false
  in
  List.for_all (List.exists litteral_true) f
;;

let gen_potential_unit_clause c =
  let rec aux u v =
    match v with
    |[] -> []
    |l::ls -> (l,u@ls)::(aux (l::u) ls)
  in
  aux [] c
;;

let find_unit_clause f m =
  try
    List.iter (fun (l,c) -> if not(is_defined_in_model l m)
                               && satisfied_by_model (negate_clause c) m then
                              raise (Unit_clause_found (l,c)))
              (List.concat (List.map gen_potential_unit_clause f));
    None
  with Unit_clause_found (l,c) -> Some (l,c)
;;

let find_litteral_undefined m n scores =
  let rec aux i out =
    if i > n then
      List.hd (List.sort (fun x y -> let ind1 = if x.negation then x.id * 2 else x.id in
                                     let ind2 = if y.negation then y.id * 2 else y.id in
                                     -1 * (compare scores.(ind1) scores.(ind2))) out)
    else
      let new_out = if is_defined_in_model {id = i; negation = true} m then out else {id = i; negation = true}::out in
      let new_new_out = if is_defined_in_model {id = i; negation = false} m then out else {id = i; negation = false}::new_out in
      aux (i+1) new_new_out
  in
  aux 1 []
;;

let add_clause_to_CNF backjump_clause f =
  let equal_clause c1 c2 = List.for_all (fun x -> List.mem x c2) c1 && List.length c1 = List.length c2 in
  if List.exists (fun x -> equal_clause backjump_clause x) f then
    f
  else
    backjump_clause::f
;;

let unsatisfiable_by_model f m =
  let litteral_false l =
    match value_of_litteral_in_model l m with
    |Some false -> true
    |_ -> false
  in
  let rec aux f =
    match f with
    |[] -> None
    |head::tail ->
      if List.for_all litteral_false head then
        Some(head)
      else
        aux tail
  in
  aux f
;;

let count_decision_litteral c level curr_level =
  List.fold_left (fun tmp l -> if LevelMap.find l.id level = curr_level then 1+tmp else tmp) 0 c
;;

let reorder_backjump_clause c level curr_level =
  let rec aux c out =
    match c with
    |[] -> raise Undefined_behaviour
    |head::tail ->
      if LevelMap.find head.id level = curr_level then
        (head, (List.rev_append tail out))
      else
        aux tail (head::out)
  in
  aux c []
;;

let rec is_infered l m =
  match m with
  |[] -> false
  |head::tail ->
    if head.var.id = l.id then
      head.inferred
    else
      is_infered l tail
;;

let merge_clause c1 c2 =
  let rec aux c1 c2 out =
    match c1 with
    |[] -> List.rev_append out c2
    |head::tail ->
      if List.mem head c2 then
        aux tail c2 out
      else
        aux tail c2 (head::out)
  in
  aux c1 c2 []
;;

let sort_clause cc m =
  let rec pos l m out =
    match m with
    |[] -> -1
    |head::tail ->
      if head.var.id = l.id then
        out
      else
        pos l tail (out+1)
  in
  fst (List.split (List.sort (fun x y -> compare (snd x) (snd y)) (List.map (fun l -> (l, pos l m 0)) cc)))
;;

let find_backjump_clause f m cc antecedent level curr_level scores = 
  let rec aux cc =
    if count_decision_litteral cc level curr_level < 2 (* && List.for_all (fun l -> is_defined_in_model l m) cc *) then
      reorder_backjump_clause cc level curr_level
    else begin
      match cc with
      |[] -> raise Undefined_behaviour
      |head::tail ->
        if is_infered head m then begin
          let ind = if head.negation then head.id * 2 else head.id in
          scores.(ind) <- scores.(ind) + 1;
          aux (merge_clause tail (AnteMap.find head.id antecedent))
        end
        else
          aux (List.rev_append (List.rev tail) [head])
    end
  in
  aux (sort_clause cc m)
;;

let find_submodel_backjump c m =
  let rec go_to_next_decision m out =
    match m with
    |[] -> ([], out)
    |head::tail ->
      if head.inferred then
        go_to_next_decision tail (head::out)
      else
        (m, out)
  in
  let rec aux m out curr_level =
    if unsatisfiable_by_model [c] out <> None then
      curr_level, Some(out)
    else begin
      match m with
      |[] -> 0, None
      |_ ->
        let new_m, new_out = go_to_next_decision (List.tl m) ((List.hd m)::out) in
        aux new_m new_out (curr_level+1)
    end
  in
  let init_m, init_out = go_to_next_decision (List.rev m) [] in
  if init_m = [] then
    0, None
  else 
    aux init_m init_out 0
;;

(**************************)
(* Satisfiability modulo theory of a model *)
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
        aux tail ((Eq(x, y))::out)
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
    false, memo_res, ((Not_eq(x, y))::l_eq_conflict)
;;

(**************************)
(* SMT solver *)
let smt_solver f =
  let cnf_f, tab_id = to_CNF (order_ast f) in
  let nb_var = nb_var_CNF cnf_f in
  let scores = Array.make ((nb_var+1)*2) 0 in
  let rec aux f m antecedent level curr_level =
    if satisfied_by_model f m then begin
      let m_theory = model_to_theory m tab_id in
      let ans, memo, conflict_theory = is_satisfiable_mod_theory empty_memo m_theory in
      if ans then
        true
      else begin
        let conflict_clause = theory_to_CNF conflict_theory tab_id [] in
        let new_litteral, new_conflict = find_backjump_clause f m conflict_clause antecedent level curr_level scores in
        let backjump_clause = new_litteral::new_conflict in
        let new_f = add_clause_to_CNF backjump_clause f in
        List.iter (fun l -> let ind = if l.negation then l.id * 2 else l.id in scores.(ind) <- scores.(ind) + 1) backjump_clause;
        match find_submodel_backjump new_conflict m with
        |_, None -> false (* UNSAT *)
        |new_curr_level, Some(new_model) ->
          aux new_f
              ({var = new_litteral; inferred = true}::new_model)
              (AnteMap.add new_litteral.id new_conflict antecedent)
              (LevelMap.add new_litteral.id new_curr_level level)
              new_curr_level
      end
    end
    else begin
      match unsatisfiable_by_model f m with
      |Some(conflict_clause) -> begin (* BACKJUMP *)
          let new_litteral, new_conflict = find_backjump_clause f m conflict_clause antecedent level curr_level scores in
          let backjump_clause = new_litteral::new_conflict in
          let new_f = add_clause_to_CNF backjump_clause f in
          List.iter (fun l -> let ind = if l.negation then l.id * 2 else l.id in scores.(ind) <- scores.(ind) + 1) backjump_clause;
          match find_submodel_backjump new_conflict m with
          |_, None -> false (* UNSAT *)
          |new_curr_level, Some(new_model) ->
            aux new_f
                ({var = new_litteral; inferred = true}::new_model)
                (AnteMap.add new_litteral.id new_conflict antecedent)
                (LevelMap.add new_litteral.id new_curr_level level)
                new_curr_level
        end
      |None -> begin
        match find_unit_clause f m with
        |None -> (* DECIDE *)
          let new_var = find_litteral_undefined m nb_var scores in
          aux f ({var = new_var; inferred = false}::m) antecedent (LevelMap.add new_var.id (curr_level+1) level) (curr_level+1)
        |Some (l,c) -> (* UNIT *)
          aux f ({var = l; inferred = true}::m) (AnteMap.add l.id c antecedent) (LevelMap.add l.id curr_level level) curr_level
      end
    end
  in
  aux cnf_f [] (AnteMap.empty) (LevelMap.empty) 0
;;



(*
(* Satisfiability modulo theory of a model *)




let _ =
  let ex = [Eq(1, 2) ; Eq(2, 5) ; Eq(3, 4) ; Not_eq(2, 4)] in
  let ans, memo, conflict = is_satisfiable_mod_theory empty_memo ex in
  print_endline (string_of_bool ans);
  print_eq conflict *)



















































(* let rec test str answer i fin out =
  if i > fin then
    out
  else
    let f = read_SAT (str ^ (string_of_int i) ^ ".cnf") in
    printf "Test numero %d : " i; flush stdout;
    if sat_solver_backjump f = answer then begin
      printf "OK\n"; flush stdout;
      test str answer (i+1) fin (out+1)
    end
    else begin
      printf "FAIL\n"; flush stdout;
      test str answer (i+1) fin out
    end
;;

let _ =
  printf "Test Positif 50 variables : \n"; flush stdout;
  let tmp = test "test1/50_yes_" true 1 16 0 in
  printf "%d/16 tests reussis\n" tmp; flush stdout;
  printf "Test Negatif 50 variables : \n"; flush stdout;
  let tmp = test "test1/50_no_" false 1 8 0 in
  printf "%d/8 tests reussis\n" tmp; flush stdout;
  printf "Test Positif 100 variables : \n"; flush stdout;
  let tmp = test "test1/100_yes_" true 1 16 0 in
  printf "%d/16 tests reussis\n" tmp; flush stdout;
  printf "Test Negatif 100 variables : \n"; flush stdout;
  let tmp = test "test1/100_no_" false 1 8 0 in
  printf "%d/8 tests reussis\n" tmp; flush stdout;
  printf "Test Positif 200 variables : \n"; flush stdout;
  let tmp = test "test1/200_yes_" true 1 16 0 in
  printf "%d/16 tests reussis\n" tmp; flush stdout;
  printf "Test Negatif 200 variables : \n"; flush stdout;
  let tmp = test "test1/200_no_" false 1 8 0 in
  printf "%d/8 tests reussis\n" tmp; flush stdout;
;; *)






















