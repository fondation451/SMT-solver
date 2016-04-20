open Printf;;
open Scanf;;

type litteral = {id : int; negation : bool};;

type clause = litteral list;;

type cnf = clause list;;

type model_var = {var : litteral; inferred : bool};;

type model = model_var list;;

exception Unit_clause_found of litteral * clause;;

exception Undefined_litteral_found of litteral;;

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

let print_model m =
  let rec aux m =
    match m with
    |[] -> ()
    |l::ls ->
      if l.var.negation = true then print_string "n";
      print_int l.var.id;
      if l.inferred = false then print_string "@";
      print_string " ";
      aux ls
  in
  aux m;
  print_newline ()
;;
(**************************)

let remove_litteral l c =
  let rec aux c out =
    match c with
    |[] -> List.rev out
    |head::tail ->
      if head = l then
        aux tail out
      else
        aux tail (head::out)
  in
  aux c []
;;

let rec is_defined_in_model lit m =
  match m with
  |[] -> false
  |l::ls ->
    if l.var.id = lit.id then
      true
    else is_defined_in_model lit ls
;;

let rec no_decision_litteral m =
  match m with
  |[] -> true
  |l::ls -> l.inferred && (no_decision_litteral ls)
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

let unsatisfiable_by_model f m =
  let litteral_false l =
    match value_of_litteral_in_model l m with
    |Some false -> true
    |_ -> false
  in
  List.exists (List.for_all litteral_false) f
;;

let negate_litteral l =
  {id = l.id; negation = not l.negation}
;;

let rec negate_clause c =
  match c with
  |[] -> []
  |l::ls -> [negate_litteral l]::(negate_clause ls)
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

let find_litteral_undefined f m =
  try
    List.iter (fun c -> List.iter (fun l -> if not (is_defined_in_model l m) then raise (Undefined_litteral_found l)) c) f;
    assert false
  with Undefined_litteral_found l -> {id = l.id; negation = false}
;;

let rec switch_first_decision_var m =
  match m with
  |[] -> []
  |l::ls ->
    if l.inferred then
      switch_first_decision_var ls
    else
      {var = negate_litteral l.var; inferred = true}::ls
;;

let rec sat_solver_backtrack f m =
  print_model m;
  if satisfied_by_model f m then
    print_endline "SAT"
  else if unsatisfiable_by_model f m && no_decision_litteral m then
    print_endline "UNSAT"
  else if unsatisfiable_by_model f m then
    sat_solver_backtrack f (switch_first_decision_var m)
  else begin
    match find_unit_clause f m with
    |None -> sat_solver_backtrack f ({var = (find_litteral_undefined f m); inferred = false}::m)
    |Some (l,c) -> sat_solver_backtrack f ({var = l; inferred = true}::m)
  end
;;

(**************************)

(* Find the Backjump clause using a resolution *)

exception Undefined_behaviour;;

let get_decision_level m =
  let rec aux m out =
    match m with
    |[] -> out
    |head::tail ->
      if head.inferred then
        aux tail (head.var::out)
      else
        (head.var::out)
  in
  aux m []
;;

let count_decision_litteral c decision_litteral =
  List.fold_left
    (fun tmp l ->
      if List.exists (fun tmp_l -> tmp_l.id = l.id) decision_litteral then
        tmp + 1
      else
        tmp
      ) 0 c
;;

let reorder_backjump_clause c decision_litteral =
  let rec aux c out =
    match c with
    |[] -> out
    |head::tail ->
      if List.exists (fun l -> l.id = head.id) decision_litteral then
        head::(List.rev_append tail out)
      else
        aux tail (head::out)
  in
  aux c []
;;

let remove_litteral_from_clause l c =
  let rec aux c out =
    match c with
    |[] -> out
    |head::tail ->
      if head.id = l.id then
        List.rev_append out tail
      else
        aux tail (head::out)
  in
  aux c []
;;

let rec find_clause_resolve l f =
  match f with
  |[] -> None
  |head::tail ->
    if List.exists (fun c_l -> l.id = c_l.id && l.negation = not c_l.negation) head then
      Some (remove_litteral_from_clause l head)
    else
      find_clause_resolve l tail
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

let append_litterals l1 l2 m =
  let rec aux l1 l2 out =
    match l2 with
    |[] -> l1, out
    |head::tail ->
      if List.mem head l1 then
        aux l1 tail out
      else if List.mem {id = head.id; negation = not head.negation} l1 then
        aux (remove_litteral {id = head.id; negation = not head.negation} l1) tail out
        (*else if List.exists (fun l -> l.var.id = head.id) m then
        aux tail (head::out)*)
      else
        aux l1 tail out
  in
  let new_l1, new_l2 = aux l1 l2 [] in
  List.rev_append (List.rev l1) new_l2
;;

let find_backjump_clause f m cc = 
  let decision_litteral = get_decision_level m in
  (* print_clause decision_litteral; print_newline (); *)
  let rec aux cc =
    (* print_clause cc; print_newline (); *)
    if count_decision_litteral cc decision_litteral < 2 (* && List.for_all (fun l -> is_defined_in_model l m) cc *) then
      (* (printf "FIN\n"; *)
      reorder_backjump_clause cc decision_litteral
    else begin
      match cc with
      |[] -> raise Undefined_behaviour
      |head::tail -> begin
        match find_clause_resolve head f with
        |Some(c) -> aux (append_litterals tail c m)
        |_ -> aux (List.rev_append (List.rev tail) [head])
      end
    end
  in
  aux (sort_clause cc m)
;;

(**************************)

(**************************)
(* SAT solver with backjump *)

(* let unsatisfiable_by_model_bis c m =
  let tmp = List.map (fun l -> value_of_litteral_in_model l m) c in
  if List.for_all (fun x -> x = Some(false)) tmp then
    true
  else
    false
;; *)

let unsatisfiable_by_model_backjump f m =
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
  let rec aux m out =
    (* printf "M1::l = \n";
    print_model m;
    printf "M2 = \n";
    print_model out; *)
    if unsatisfiable_by_model [c] out then
      Some(out)
    else begin
      match m with
      |[] -> None
      |_ ->
        let new_m, new_out = go_to_next_decision (List.tl m) ((List.hd m)::out) in
        aux new_m new_out
    end
  in
  (* printf "Debut de la recherche du nouveau modele !\n"; *)
  let init_m, init_out = go_to_next_decision (List.rev m) [] in
  if init_m = [] then
    None
  else 
    aux init_m init_out
;;

let rec sat_solver_backjump f m =
  print_model m;
  if satisfied_by_model f m then
    print_endline "SAT"
  else begin
    match unsatisfiable_by_model_backjump f m with
    |Some(conflict_clause) -> begin
        (* printf "Backjump !!!\n";
        printf "Conflict clause : ";
        print_CNF [conflict_clause]; print_newline (); printf "-------\n"; *)
        let backjump_clause = find_backjump_clause f m conflict_clause in
        (* printf "fin Backjump !!!\n";
        printf "Backjump clause : ";
        print_CNF [backjump_clause]; print_newline (); printf "-------\n"; *)
        let new_litteral = List.hd backjump_clause in
        let new_conflict = List.tl backjump_clause in
        (* printf "Nouveau conflit : ";
        print_CNF [new_conflict]; print_newline (); printf "-------\n"; *)
        match find_submodel_backjump new_conflict m with
        |None -> print_endline "UNSAT"
        |Some(new_model) -> sat_solver_backjump f ({var = new_litteral; inferred = true}::new_model)
      end
    |None -> begin
      match find_unit_clause f m with
      |None -> sat_solver_backjump f ({var = (find_litteral_undefined f m); inferred = false}::m)
      |Some (l,c) -> sat_solver_backjump f ({var = l; inferred = true}::m)
    end
  end
;;

(**************************)

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

(**************************)



let () =
  let l0 = {id = 0; negation = false} in
  let l1 = {id = 1; negation = false} in
  let l2 = {id = 2; negation = false} in
  let l3 = {id = 3; negation = false} in
  let l4 = {id = 4; negation = false} in
  let l5 = {id = 5; negation = false} in
  let l6 = {id = 6; negation = false} in
  let l7 = {id = 7; negation = false} in
  let l8 = {id = 8; negation = false} in
  let l9 = {id = 9; negation = false} in
  let l10 = {id = 10; negation = false} in
  let l11 = {id = 11; negation = false} in
  let l12 = {id = 12; negation = false} in
  let l13 = {id = 13; negation = false} in
  let l14 = {id = 14; negation = false} in
  let l15 = {id = 15; negation = false} in
  let l16 = {id = 16; negation = false} in
  let l17 = {id = 17; negation = false} in
  let l18 = {id = 18; negation = false} in
  let l19 = {id = 19; negation = false} in
  let l20 = {id = 20; negation = false} in
  let l0n = {id = 0; negation = true} in
  let l1n = {id = 1; negation = true} in
  let l2n = {id = 2; negation = true} in
  let l3n = {id = 3; negation = true} in
  let l4n = {id = 4; negation = true} in
  let l5n = {id = 5; negation = true} in
  let l6n = {id = 6; negation = true} in
  let l7n = {id = 7; negation = true} in
  let l8n = {id = 8; negation = true} in
  let l9n = {id = 9; negation = true} in
  let l10n = {id = 10; negation = true} in
  let l11n = {id = 11; negation = true} in
  let l12n = {id = 12; negation = true} in
  let l13n = {id = 13; negation = true} in
  let l14n = {id = 14; negation = true} in
  let l15n = {id = 15; negation = true} in
  let l16n = {id = 16; negation = true} in
  let l17n = {id = 17; negation = true} in
  let l18n = {id = 18; negation = true} in
  let l19n = {id = 19; negation = true} in
  let l20n = {id = 20; negation = true} in
 let example =
   [
     [l9n;l3;l4;l5n;l18n;l11;l1n;l10;l12;l16 ];
   [l19n;l15n;l12n;l16;l20n;l4n;l3n;l5n;l8;l13n];
   [l14n;l9n;l1n;l5n;l12n;l3n;l4n;l6n;l17n;l16];
   [l8n;l1;l16;l10n;l4;l2n;l6n;l9n;l3n;l19];
   [l2n;l9;l13;l7n;l8n;l17;l19;l4;l11n;l14];
   [l5;l18n;l17;l19;l4;l20;l14n;l9;l2;l7];
   [l6n;l13;l3n;l11;l4;l19;l1n;l2n;l17n;l16n];
   [l20;l11;l7;l4n;l15;l1n;l17;l12n;l13n;l18];
   [l13n;l8n;l5n;l4n;l20n;l2;l9;l16n;l6n;l10n];
   [l6;l3n;l2n;l1;l7n;l10n;l19n;l17;l15n;l12n]
   ]
  in
  let example2 =
  [[l6; l8; l1n; l3];
  [l7; l9n];
  [l8; l4];
  [l9n; l7n; l4n];
  [l8; l1n; l7n];
  [l3; l4];
  [l4n; l8n; l6n];
  [l2; l9; l3n; l4];
  [l3n; l2; l6];
  [l4n; l9n];
  [l2n; l1n; l5];
  [l4n; l2; l5n; l1];
  [l6; l7n; l4n];
  [l7n; l1n];
  [l6; l8n]]
  in
  
  (*sat_solver_backtrack example [];
  let f = [[l9n;l6n;l7;l8n];[l8;l7;l5n];[l6n;l8;l4];[l4n;l1n];[l4n;l5;l2];[l5;l7;l3n];[l1;l2n;l3]] in
  let m = [{var = l3n ; inferred = true};{var = l2 ; inferred = true};{var = l1n ; inferred = true};{var = l4 ; inferred = true};
  {var = l5n ; inferred = true};{var = l8n ; inferred = true};{var = l9 ; inferred = false};{var = l4 ; inferred = true}] in
  let cc = [l1;l2n;l3] in
  let f = [[l1n;l2];[l3n;l4];[l5n;l6n];[l6;l5n;l2n];[l5;l7];[l5;l7n;l2n]] in
  let m = [{var = l6n ; inferred = true};{var = l5 ; inferred = false};{var = l4 ; inferred = true};{var = l3 ; inferred = false};
  {var = l2 ; inferred = true};{var = l1 ; inferred = false}] in
  let cc = [l6;l5n;l2n] in
  printf "Debut des calcul de backjump clause\n";
  let backjump_clause = find_backjump_clause f m cc in
  printf "Formule : ";
  print_CNF f; print_newline ();
  printf "Modele : ";
  print_model m; print_newline ();
  printf "Backjump_clause : ";
  print_CNF [backjump_clause]; print_newline ();*)
  let f = [[l1n;l2];[l3n;l4];[l5n;l6n];[l6;l5n;l2n];[l5;l7];[l5;l7n;l2n]] in
(*  printf "SAT Solver with Backtrack : \n";
  sat_solver_backtrack f [];
  printf "\n\nSAT Solver with Backtjump : \n";
  sat_solver_backjump f [];
  *)
  printf "\n\nEssaie numéro 2 !!!!!!!\n";
  printf "SAT Solver with Backtrack : \n";
  sat_solver_backtrack f [];
  printf "\n\nSAT Solver with Backtjump : \n";
  sat_solver_backjump f [];
  
  let example3 = read_SAT "aim/aim-50-1_6-no-1.cnf" in
  printf "\n\nEssaie numéro 3 !!!!!!!\n";
  (*printf "SAT Solver with Backtrack : \n";
  sat_solver_backtrack example3 [];*)
  printf "\n\nSAT Solver with Backtjump : \n";
  sat_solver_backjump example3 []
;;























