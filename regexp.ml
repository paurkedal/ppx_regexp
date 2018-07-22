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

let mkloc = Location.mkloc

type 'a t = 'a node Location.loc
and 'a node =
  | Code of 'a
  | Seq of 'a t list
  | Alt of 'a t list
  | Opt of 'a t
  | Repeat of (int * int option) Location.loc * 'a t
  | Capture of 'a t
  | Capture_as of string Location.loc * 'a t
  | Call of Longident.t Location.loc
  (* TODO: | Case_sense of t | Case_blind of t *)

let nonepsilon = function {Location.txt = Seq []; _} -> false | _ -> true

let simplify_seq ~loc es =
  (match List.filter nonepsilon es with
   | [e] -> e
   | es -> mkloc (Seq es) loc)

let simplify_alt es =
  (match es with
   | [e] -> e.Location.txt
   | es -> Alt es)

module Int_map = Map.Make (struct type t = int let compare = compare end)

let parse_exn ?(pos = Lexing.dummy_pos) s =
  let l = String.length s in
  let get i = if i = l then ')' else s.[i] in

  (* Location Tracking *)
  let position_of_index =
    if pos = Lexing.dummy_pos then (fun _ -> Lexing.dummy_pos) else
    let newlines =
      let rec loop acc lnum i =
        if i = l then acc else
        if s.[i] <> '\n' then loop acc lnum (i + 1) else
        loop (Int_map.add (i + 1) (lnum + 1) acc) (lnum + 1) (i + 1)
      in
      loop (Int_map.singleton 0 pos.pos_lnum) pos.pos_lnum pos.pos_bol
    in
    fun i ->
      let j, pos_lnum = Int_map.find_last (fun j -> j <= i) newlines in
      { pos with
        pos_lnum;
        pos_bol = pos.pos_bol + j;
        pos_cnum = pos.pos_cnum + i; }
  in
  let make_loc (i, j) =
    let open Location in
    if pos = Lexing.dummy_pos then Location.none else
    { loc_start = position_of_index i;
      loc_end = position_of_index j;
      loc_ghost = false }
  in
  let wrap_loc (i, j) x = Location.{txt = x; loc = make_loc (i, j)} in
  let with_loc f i = let j, e = f i in j, wrap_loc (i, j) e in

  let fail (i, j) msg = Location.raise_errorf ~loc:(make_loc (i, j)) "%s" msg in

  (* Identifiers *)
  let rec scan_ident i j =
    if j = l then fail (i, j) "Unterminated named capture." else
    (match s.[j] with
     | 'A'..'Z' | '0'..'9' when i = j ->
        fail (i, j + 1) "Invalid identifier first char."
     | 'A'..'Z' | '0'..'9' | 'a'..'z' | '_' ->
        scan_ident i (j + 1)
     | _ when i = j ->
        fail (i, i) "Missing identifier."
     | _ ->
        (j, wrap_loc (i, j) (String.sub s i (j - i))))
  in
  let scan_longident i =
    let rec loop j =
      (match get j with
       | 'A'..'Z' | 'a'..'z' | '0'..'9' | '_' | '.' -> loop (j + 1)
       | _ -> (j, Longident.parse (String.sub s i (j - i))))
    in
    loop i (* TODO: Which exception to catch? *)
  in

  (* Non-Nested Parts *)
  let re_perl (i, j) = wrap_loc (i, j) (Code (String.sub s i (j - i))) in
  let scan_escape i =
    if i + 1 = l then fail (i, i+1) "Escape at end of regular expression." else
    (match s.[i + 1] with
     | 'a'..'z' | 'A'..'Z' -> (i + 2, re_perl (i, i + 2))
     | _ -> (i + 2, re_perl (i, i + 2)))
  in
  let rec scan_cset i j =
    if j = l then fail (i, i + 1) "Unbalanced '['." else
    (match s.[j] with
     | '\\' -> scan_cset i (j + 2)
     | '[' ->
        (match String.index_from_opt s (j + 1) ']' with
         | None -> fail (j + 1, j + 2) "Unbalanced '[' in character set."
         | Some k -> scan_cset i (k + 1))
     | ']' -> (j + 1, re_perl (i, j + 1))
     | _ -> scan_cset i (j + 1))
  in

  (* Repeat and Opt *)
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
        (j, n_min, (Some n_min)))
  in
  let rep_hd i j n_min n_max = function
   | [] -> fail (i, j) "Operator must follow an operand."
   | (e : _ Location.loc) :: es ->
      let loc = Location.{
        loc_start = e.loc.loc_start;
        loc_end = position_of_index j;
        loc_ghost = false;
      } in
      mkloc (Repeat (wrap_loc (i, j) (n_min, n_max), e)) loc :: es
  in
  let opt_hd i = function
   | [] -> fail (i, i + 1) "Operator must follow an operand."
   | (e : _ Location.loc) :: es ->
      let loc = Location.{
        loc_start = e.loc.loc_start;
        loc_end = position_of_index (i + 1);
        loc_ghost = false;
      } in
      mkloc (Opt e) loc :: es
  in

  (* Sequences and Groups *)
  let
    rec scan_alt i =
      let j, e = scan_alt_item i [] in
      (j, simplify_alt e)
    and scan_alt_item i acc =
      let j, e = scan_seq i in
      (match get j with
       | ')' -> (j, List.rev (e :: acc))
       | '|' -> scan_alt_item (j + 1) (e :: acc)
       | _ -> assert false)

    and scan_seq i =
      let j, e = scan_seq_item i [] in
      (j, simplify_seq ~loc:(make_loc (i, j)) e)
    and scan_seq_item i acc =
      (match get i with
       | ')' | '|' -> (i, List.rev acc)
       | '[' ->
          let j, e = scan_cset i (i + 1) in
          scan_seq_item j (e :: acc)
       | ('?' | '*' | '+') when get (i + 1) = '?' ->
          fail (i, i + 1) "Greedyness modifier not implemented."
        (* TODO: Reject nested cases which require paretheses in PCRE.
         * TODO: Reject repetition of ε and zero-width assertions. *)
       | '?' -> scan_seq_item (i + 1) (opt_hd i acc)
       | '*' -> scan_seq_item (i + 1) (rep_hd i (i + 1) 0 None acc)
       | '+' -> scan_seq_item (i + 1) (rep_hd i (i + 1) 1 None acc)
       | '{' ->
          let j, n_min, n_max = scan_range (i + 1) in
          if j = l || s.[j] <> '}' then fail (i, i + 1) "Unbalanced '{'." else
          scan_seq_item (j + 1) (rep_hd i (j + 1) n_min n_max acc)
       | '(' ->
          let j, e = scan_group (i + 1) in
          if j = l || s.[j] <> ')' then fail (i, i + 1) "Unbalanced '('." else
          scan_seq_item (j + 1) (wrap_loc (i, j + 1) e :: acc)
       | '^' -> scan_seq_item (i + 1) (re_perl (i, i + 1) :: acc)
       | '$' -> scan_seq_item (i + 1) (re_perl (i, i + 1) :: acc)
       | '\\' ->
          let j, e = scan_escape i in
          scan_seq_item j (e :: acc)
       | _ -> scan_seq_item (i + 1) (re_perl (i, i + 1) :: acc))

    and scan_group i =
      (match get i with
       | '?' ->
          if i + 1 = l then fail (i - 1, i) "Unbalanced '('." else
          (match s.[i + 1] with
           | '&' ->
              let j, idr = with_loc scan_longident (i + 2) in
              (j, Call idr)
           | '<' ->
              let j, idr = scan_ident (i + 2) (i + 2) in
              if get j <> '>' then fail (i, i + 1) "Unbalanced '<'." else
              let k, e = with_loc scan_alt (j + 1) in
              (k, Capture_as (idr, e))
           | ':' ->
              scan_alt (i + 2)
           | _ ->
              fail (i, i + 2) "Invalid group modifier.")
       | '+' -> let j, e = with_loc scan_alt (i + 1) in (j, Capture e)
       | '*' | '{' -> fail (i, i + 1) "Invalid group modifier."
       | _ -> scan_alt i)
  in

  (* Top-Level *)
  let j, e = with_loc scan_alt 0 in
  if j <> l then fail (j, j + 1) "Unbalanced ')'." else e

let parse ?pos s =
  try Ok (parse_exn ?pos s) with Location.Error error -> Error error
