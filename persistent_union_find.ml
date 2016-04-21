(* Module taken from the work of Sylvain Conchon 
 *                            and Jean-Christophe Filliatre *)

type t = {
  rank: int Persistent_array.t;
  mutable parent: int Persistent_array.t
}

let create n = {
  rank = Persistent_array.init n (fun _ -> 0);
  parent = Persistent_array.init n (fun i -> i)
}

let rec find_aux f i =
  let fi = Persistent_array.get f i in
  if fi == i then
    f, i
  else
    let f, r = find_aux f fi in
    let f = Persistent_array.set f i r in
    f, r

let find h x =
  let f,cx = find_aux h.parent x in
  h.parent <- f;
  cx

let union h x y =
  let cx = find h x in
  let cy = find h y in
  if cx != cy then begin
    let rx = Persistent_array.get h.rank cx in
    let ry = Persistent_array.get h.rank cy in
    if rx > ry then
      { h with parent = Persistent_array.set h.parent cy cx }
    else if rx < ry then
      { h with parent = Persistent_array.set h.parent cx cy }
    else
      { rank = Persistent_array.set h.rank cx (rx + 1);
        parent = Persistent_array.set h.parent cy cx }
  end else
    h
