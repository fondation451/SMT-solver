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
  if satisfied_by_model f m then
    true (* SAT *)
  else if unsatisfiable_by_model f m && no_decision_litteral m then
    false (* UNSAT *)
  else if unsatisfiable_by_model f m then
    sat_solver_backtrack f (switch_first_decision_var m)
  else begin
    match find_unit_clause f m with
    |None -> sat_solver_backtrack f ({var = (find_litteral_undefined f m); inferred = false}::m)
    |Some (l,c) -> sat_solver_backtrack f ({var = l; inferred = true}::m)
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



let rec test str answer i fin out =
  if i > fin then
    out
  else
    let f = read_SAT (str ^ (string_of_int i) ^ ".cnf") in
    printf "Test numero %d : " i; flush stdout;
    if sat_solver_backtrack f [] = answer then begin
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
;;




















