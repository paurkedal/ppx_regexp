(* Copyright (C) 2018  Petter A. Urkedal <paurkedal@gmail.com>
 *
 * This library is free software; you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or (at your
 * option) any later version, with the OCaml static compilation exception.
 *
 * This library is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public
 * License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this library.  If not, see <http://www.gnu.org/licenses/>.
 *)

type t =
  | Re of Re.t
  | Seq of t list
  | Alt of t list
  | Opt of t
  | Repeat of int * int option * t
  | Capture of t
  | Capture_as of string * t
  | Call of Longident.t Location.loc
  (* TODO: | Case_sense of t | Case_blind of t *)

type error = {pos: int; msg: string}

exception Parse_error of error

let fail pos msg = raise (Parse_error {pos; msg})

let rep_hd i n_min n_max = function
 | [] -> fail i "Operator must follow an operand."
 | Repeat _ :: _ -> fail i "Nested repetition."
 | e :: es -> Repeat (n_min, n_max, e) :: es

let opt_hd i = function
 | [] -> fail i "Operator must follow an operand."
 | Repeat _ :: _-> fail i "Greedyness modifier not implemented."
 | e :: es -> Opt e :: es

let simplify_seq es =
  (match List.filter (function Seq [] -> false | _ -> true) es with
   | [e] -> e
   | es -> Seq es)

let simplify_alt es =
  (match es with
   | [e] -> e
   | es -> Alt es)

let parse s =
  let l = String.length s in
  let get i = if i = l then ')' else s.[i] in

  (* Identifiers *)
  let rec scan_ident i j =
    if j = l then fail i "Unterminated named capture." else
    (match s.[j] with
     | 'A'..'Z' | '0'..'9' when i = j ->
        fail i "Invalid identifier first char."
     | 'A'..'Z' | '0'..'9' | 'a'..'z' | '_' ->
        scan_ident i (j + 1)
     | _ when i = j ->
        fail i "Missing identifier."
     | _ ->
        (j, String.sub s i (j - i)))
  in
  let scan_longident i =
    let rec loop j =
      (match get j with
       | 'A'..'Z' | 'a'..'z' | '0'..'9' | '_' | '.' -> loop (j + 1)
       | _ -> (j, Longident.parse (String.sub s i j)))
    in
    loop i (* TODO: Which exception to catch? *)
  in

  (* Non-Nested Parts as Re.t *)
  let scan_re ~msg i j =
    try (j, Re (Re.Perl.re (String.sub s i (j - i)))) with
     | Re.Perl.Parse_error -> fail i msg
  in
  let rec scan_str i j =
    (match get j with
     | '[' | '?' | '*' | '+' | '{' | '(' | ')' | '|' | '\\' ->
        (j, Re (Re.str (String.sub s i (j - i))))
     | _ -> scan_str i (j + 1))
  in
  let scan_escape i =
    if i + 1 = l then fail i "Escape at end of regular expression." else
    (match s.[i + 1] with
     | 'a'..'z' | 'A'..'Z' ->
        scan_re ~msg:"Invalid escape instruction." i (i + 2)
     | ch -> (i + 2, Re (Re.char ch)))
  in
  let rec scan_cset i j =
    if j = l then fail j "Unbalanced '['." else
    (match s.[j] with
     | '\\' -> scan_cset i (j + 2)
     | '[' ->
        (match String.index_from_opt s (j + 1) ']' with
         | None -> fail j "Unbalanced '[' in character set."
         | Some k -> scan_cset i (k + 1))
     | ']' -> scan_re ~msg:"Invalid character set." i (j + 1)
     | _ -> scan_cset i (j + 1))
  in

  (* Repeat Ranges *)
  let scan_int_opt i =
    let rec loop i n =
      if i = l then (i, n) else
      (match s.[i] with
       | '0'..'9' as ch -> loop (i + 1) (10 * n + (Char.code ch - 48))
       | _ -> (i, n))
    in
    let j, n = loop i 0 in
    (j, (if i = j then None else Some n))
  in
  let scan_range i =
    let j, n_min = scan_int_opt i in
    let n_min = match n_min with None -> 0 | Some n -> n in
    (match get j with
     | ',' ->
        let j, n_max = scan_int_opt (j + 1) in
        (j, n_min, n_max)
     | _ ->
        (j, n_min, Some n_min))
  in

  (* Sequences and Groups *)
  let
    rec scan_alt i acc =
      let j, e = scan_seq i [] in
      (match get j with
       | ')' -> (j, simplify_alt (List.rev (e :: acc)))
       | '|' -> scan_alt (j + 1) (e :: acc)
       | _ -> assert false)
    and scan_seq i acc =
      (match get i with
       | ')' | '|' -> (i, simplify_seq (List.rev acc))
       | '[' ->
          let j, e = scan_cset i (i + 1) in
          scan_seq j (e :: acc)
       | '?' -> scan_seq (i + 1) (opt_hd i acc)
       | '*' -> scan_seq (i + 1) (rep_hd i 0 None acc)
       | '+' -> scan_seq (i + 1) (rep_hd i 1 None acc)
       | '{' ->
          let j, n_min, n_max = scan_range (i + 1) in
          if j = l || s.[j] <> '}' then fail i "Unbalanced '{'." else
          scan_seq j (rep_hd i n_min n_max acc)
       | '(' ->
          let j, e = scan_group (i + 1) in
          if j = l || s.[j] <> ')' then fail i "Unbalanced '('." else
          scan_seq (j + 1) (e :: acc)
       | '^' -> scan_seq (i + 1) (Re Re.bos :: acc)
       | '$' -> scan_seq (i + 1) (Re Re.eos :: acc)
       | '\\' ->
          let j, e = scan_escape i in
          scan_seq j (e :: acc)
       | _ ->
          let j, e = scan_str i i in
          scan_seq j (e :: acc))
    and scan_group i =
      (match get i with
       | '?' ->
          if i + 1 = l then fail (i - 1) "Unbalanced '('." else
          (match s.[i + 1] with
           | '&' ->
              let j, idr = scan_longident (i + 2) in
              (j, Call (Location.mknoloc idr))
           | '<' ->
              let j, idr = scan_ident (i + 2) (i + 2) in
              if get j <> '>' then fail i "Unbalanced '<'." else
              let j, e = scan_alt (j + 1) [] in
              (j, Capture_as (idr, e))
           | ':' ->
              let j, e = scan_alt (i + 2) [] in (j, e)
           | _ ->
              fail (i + 1) "Invalid group modifier.")
       | '+' ->
          let j, e = scan_alt (i + 1) [] in (j, Capture e)
       | '*' | '{' ->
          fail i "Invalid operator at start of group."
       | _ ->
          scan_alt i [])
  in

  (* Top-Level *)
  try
    let j, e = scan_alt 0 [] in
    if j <> l then fail j "Unbalanced ')'." else
    Ok e
  with Parse_error error ->
    Error error
