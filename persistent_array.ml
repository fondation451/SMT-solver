(* Module taken from the work of Sylvain Conchon 
 *                            and Jean-Christophe Filliatre *)

type 'a t = 'a data ref
and 'a data =
  | Arr of int array
  | Diff of int * 'a * 'a t
  | Invalid

let init n f = ref (Arr (Array.init n f))

let rec length pa =
  match !pa with
  | Arr a -> Array.length a
  | Diff (i, v, pa') -> length pa'
  | Invalid -> assert false
  

let rec expand pa n f =
  match !pa with
  | Arr a -> ref (Arr (Array.init (Array.length a + n) 
                                  (fun i -> if i < Array.length a 
                                            then a.(i) else f i)))
  | Diff (i, v, pa') -> ref (Diff (i, v, expand pa' n f))
  | Invalid -> assert false
  

let rec reroot t = match !t with
  | Arr _ -> ()
  | Diff (i, v, t') ->
    reroot t';
    begin match !t' with
    | Arr a as n ->
      a.(i) <- v;
      t := n;
      t' := Invalid
    | Diff _ | Invalid -> assert false
    end
    | Invalid -> assert false

let set t i v =
  reroot t;
  match !t with
  | Arr a as n ->
      let old = a.(i) in
      a.(i) <- v;
      let res = ref n in
      t := Diff (i, old, res);
      res
  | Diff _ | Invalid -> assert false

let rec get t i = match !t with
  | Arr a -> a.(i)
  | Diff _ ->
    reroot t;
    begin match !t with
    | Arr a -> a.(i)
    | Diff _ | Invalid -> assert false
    end
  | Invalid -> assert false
