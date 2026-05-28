open Assertion
open SugarAux

(* name := string _ int *)
type name = string * int option

let split_char = '_'

let name_of_string name =
  let l = List.rev @@ String.split_on_char split_char name in
  match l with
  | [] -> _die_with [%here] (Printf.sprintf "not a well-formed name: %s" name)
  | id :: rest -> (
      let rest = List.rev rest in
      match int_of_string_opt id with
      | None -> (name, None)
      | Some i ->
          let rest = String.concat (spf "%c" split_char) rest in
          (rest, Some i))

let name_to_string (sname, id) =
  match id with None -> sname | Some i -> spf "%s%c%i" sname split_char i

let _unique tab (sname, id) =
  let max_one =
    match Hashtbl.find_opt tab sname with
    | Some n -> (
        match id with
        | None -> Some n
        | Some id -> if id < n then Some n else Some id)
    | None -> id
  in
  match max_one with
  | Some n ->
      Hashtbl.replace tab sname (n + 1);
      (sname, Some n)
  | None ->
      Hashtbl.add tab sname 0;
      (sname, None)
(*     let () = *)
(*       match id with *)
(*       | None -> () *)
(*       | Some id -> *)
(*         if id >= n then Hashtbl.replace tab sname (n + 1); *)
(*           _assert [%here] *)
(*             (spf "seen id (%i) should less than next available one (%i) in %s" *)
(*                id n sname) *)
(*             (id < n) *)
(*     in *)
(*     Hashtbl.replace tab sname (n + 1); *)
(*     (sname, Some n) *)
(* | None -> *)
(*     let () = *)
(*       match id with *)
(*       | None -> () *)
(*       | Some id -> *)
(*           _assert [%here] *)
(*             (spf *)
(*                "seen id (%i) should less than next available one (None) in %s" *)
(*                id sname) *)
(*             false *)
(*     in *)
(*     Hashtbl.add tab sname 0; *)
(*     (sname, None) *)

let mk_unique tab name = name_to_string @@ _unique tab @@ name_of_string name

(* NOTE: store the next available name lazily *)
let universal_type_var : (string, int) Hashtbl.t = Hashtbl.create 100
let universal_var : (string, int) Hashtbl.t = Hashtbl.create 1000
let _unique_type_var sname = _unique universal_type_var sname
let _unique_var sname = _unique universal_var sname
let unique_type_var name = mk_unique universal_type_var name
let unique_var name = mk_unique universal_var name
let dummy_var () = unique_var "dummyVar"
let dummy_type_var () = unique_var "dummyTypeVar"
let fresh_type_var () = unique_var "tv"
let fresh_var () = unique_var "tmp"

let different_var name =
  let name' = unique_var name in
  if name <> name' then name'
  else
    let name' = unique_var name in
    _assert [%here] (spf "should get a different name: %s" name) (name <> name');
    name'
