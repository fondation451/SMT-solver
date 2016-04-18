type litteral = {id : int; negation : bool}

type clause = litteral list

type cnf = clause list

type model_var = {var : litteral; inferred : bool}

type model = model_var list

exception Unit_clause_found of litteral * clause

exception Undefined_litteral_found of litteral

let rec is_defined_in_model lit m =
  match m with
  | [] -> false
  | l::ls -> if l.var.id = lit.id then true 
             else is_defined_in_model lit ls

let rec no_decision_litteral m =
  match m with
  | [] -> true
  | l::ls -> l.inferred && (no_decision_litteral ls)

let rec value_of_litteral_in_model l m =
  match m with
  | [] -> None
  | lm::ls -> if lm.var.id = l.id && lm.var.negation = l.negation
              then Some true
              else if lm.var.id = l.id
              then Some false
              else value_of_litteral_in_model l ls
  
let satisfied_by_model f m =
  let litteral_true l =
    match value_of_litteral_in_model l m with
    | Some true -> true
    | _ -> false
  in
  List.for_all (List.exists litteral_true) f

let unsatisfiable_by_model f m =
  let litteral_false l =
    match value_of_litteral_in_model l m with
    | Some false -> true
    | _ -> false
  in
  List.exists (List.for_all litteral_false) f

let negate_litteral l =
  {id = l.id; negation = not l.negation}
 
let rec negate_clause c =
  match c with
  | [] -> []
  | l::ls -> [negate_litteral l]::(negate_clause ls)
  

let gen_potential_unit_clause c =
  let rec aux u v =
    match v with
    | [] -> []
    | l::ls -> (l,u@ls)::(aux (l::u) ls)
  in
  aux [] c
    
let find_unit_clause f m =
  try
    List.iter (fun (l,c) -> if not(is_defined_in_model l m)
                            && satisfied_by_model (negate_clause c) m
                            then raise (Unit_clause_found (l,c)))
              (List.concat (List.map gen_potential_unit_clause f));
    None
  with Unit_clause_found (l,c) -> Some (l,c)

let find_litteral_undefined f m =
  try 
    List.iter (fun c -> List.iter (fun l -> if not (is_defined_in_model l m) then raise (Undefined_litteral_found l)) c) f;
    assert false
  with Undefined_litteral_found l -> l
  
let rec switch_first_decision_var m =
  match m with
  | [] -> []
  | l::ls -> if l.inferred then switch_first_decision_var ls
             else {var = negate_litteral l.var; inferred = true}::ls

let print_model m =
  let rec aux m =
    match m with
    |[] -> ()
    |l::ls ->
			if l.var.negation = true then print_string "n";
      print_int l.var.id;
			print_string " ";
			aux ls
  in
  aux m;
	print_newline ()
;;
  

let rec sat_solver f m =
  print_model m;
  if satisfied_by_model f m then
		print_endline "SAT"
  else if unsatisfiable_by_model f m && no_decision_litteral m then
		print_endline "UNSAT"
  else if unsatisfiable_by_model f m then
		sat_solver f (switch_first_decision_var m)
	else begin
		match find_unit_clause f m with
    |None -> sat_solver f ({var = (find_litteral_undefined f m); inferred = false}::m)
    |Some (l,c) -> sat_solver f ({var = l; inferred = true}::m)
	end
;;
      
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
  sat_solver example []
