(* Copyright (C) 2017  Petter A. Urkedal <paurkedal@gmail.com>
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

open Migrate_parsetree
open Ast_404
let ocaml_version = Versions.ocaml_404

open Ast_mapper
open Ast_helper
open Asttypes
open Longident
open Parsetree
open Printf

let error ~loc msg = raise (Location.Error (Location.error ~loc msg))

let warn ~loc msg e =
  let e_msg = Exp.constant (Const.string msg) in
  let structure = {pstr_desc = Pstr_eval (e_msg, []); pstr_loc = loc} in
  Exp.attr e ({txt = "ocaml.ppwarning"; loc}, PStr [structure])

module List = struct
  include List

  let rec fold f = function
   | []      -> fun acc -> acc
   | x :: xs -> fun acc -> fold f xs (f x acc)
end

module Regexp = struct
  include Regexp

  let bindings =
    let rec recurse must_match (e' : _ Location.loc) =
      let loc = e'.Location.loc in
      (match e'.Location.txt with
       | Code _ -> fun acc -> acc
       | Seq es -> List.fold (recurse must_match) es
       | Alt es -> List.fold (recurse false) es
       | Opt e -> recurse false e
       | Repeat ({Location.txt = (i, _); _}, e) ->
          recurse (must_match && i > 0) e
       | Nongreedy e -> recurse must_match e
       | Capture _ -> error ~loc "Unnamed capture is not allowed for %pcre."
       | Capture_as (idr, e) ->
          fun (nG, bs) ->
            recurse must_match e (nG + 1, (idr, Some nG, must_match) :: bs)
       | Call _ -> error ~loc "(&...) is not implemented for %pcre.")
    in
    (function
     | {Location.txt = Capture_as (idr, e); _} ->
        recurse true e (0, [idr, None, true])
     | e ->
        recurse true e (0, []))

  let to_string =
    let p_alt, p_seq, p_suffix, p_atom = 0, 1, 2, 3 in
    let delimit_if b s = if b then "(?:" ^ s ^ ")" else s in
    let rec recurse p (e' : _ Location.loc) =
      let loc = e'.Location.loc in
      (match e'.Location.txt with
       | Code s ->
          (* Delimiters not needed as Regexp.parse_exn only returns single
           * chars, csets, and escape sequences. *)
          s
       | Seq es ->
          delimit_if (p > p_seq)
            (String.concat "" (List.map (recurse p_seq) es))
       | Alt es ->
          delimit_if (p > p_alt)
            (String.concat "|" (List.map (recurse p_alt) es))
       | Opt e ->
          delimit_if (p > p_suffix) (recurse p_atom e ^ "?")
       | Repeat ({Location.txt = (i, j_opt); _}, e) ->
          let j_str = match j_opt with None -> "" | Some j -> string_of_int j in
          delimit_if (p > p_suffix)
            (sprintf "%s{%d,%s}" (recurse p_atom e) i j_str)
       | Nongreedy e -> recurse p_suffix e ^ "?"
       | Capture _ -> error ~loc "Unnamed capture is not allowed for %pcre."
       | Capture_as (_, e) -> "(" ^ recurse p_alt e ^ ")"
       | Call _ -> error ~loc "(&...) is not implemented for %pcre.")
    in
    (function
     | {Location.txt = Capture_as (_, e); _} ->
        recurse 0 e
     | e ->
        recurse 0 e)
end

let dyn_bindings = ref []
let clear_bindings () = dyn_bindings := []
let add_binding binding = dyn_bindings := binding :: !dyn_bindings
let get_bindings () = !dyn_bindings

let fresh_var =
  let c = ref 0 in
  fun () -> incr c; Printf.sprintf "_ppx_regexp_%d" !c

let rec is_zero p k =
  (match p.[k] with
   | '0' -> is_zero p (k + 1)
   | '1'..'9' -> false
   | _ -> true)

let rec must_match p i =
  let l = String.length p in
  if i = l then true else
  if p.[i] = '?' || p.[i] = '*' then false else
  if p.[i] = '{' then
    let j = String.index_from p (i + 1) '}' in
    not (is_zero p (i + 1)) && must_match p (j + 1)
  else
    true

let extract_bindings ~pos s =
  let r = Regexp.parse_exn ~pos s in
  let nG, bs = Regexp.bindings r in
  let re_str = Regexp.to_string r in
  (Exp.constant (Const.string re_str), bs, nG)

let rec wrap_group_bindings ~loc rhs offG = function
 | [] -> rhs
 | (varG, iG, mustG) :: bs ->
    let eG = match iG with
     | None ->
        [%expr Re.Group.get _g 0]
     | Some iG ->
        [%expr Re.Group.get _g [%e Exp.constant (Const.int (offG + iG + 1))]]
    in
    let eG =
      if mustG then eG else
      [%expr try Some [%e eG] with Not_found -> None]
    in
    [%expr
      let [%p Pat.var varG] = [%e eG] in
      [%e wrap_group_bindings ~loc rhs offG bs]]

let transform_cases ~loc cases =
  let aux case =
    if case.pc_guard <> None then
      error ~loc "Guards are not implemented for match%pcre." else
    (match case.pc_lhs with
     | { ppat_desc = Ppat_constant (Pconst_string (re_src, re_delim));
         ppat_loc = {loc_start; _}; _ } ->
        let re_offset =
          (match re_delim with Some s -> String.length s + 2 | None -> 1) in
        let pos = {loc_start with pos_cnum = loc_start.pos_cnum + re_offset} in
        let re, bs, nG = extract_bindings ~pos re_src in
        (re, nG, bs, case.pc_rhs)
(*
     | {ppat_desc = Ppat_alias
         ({ ppat_desc = Ppat_constant (Pconst_string (re_src,_));
            ppat_loc = loc; _ },
          var); _} ->
        let re, bs, nG = extract_bindings ~loc re_src in
        let rhs =
          (* TODO: Should this be (_ppx_regexp_v or Re.Group.get _g 0? *)
          [%expr let [%p Pat.var var] = _ppx_regexp_v in [%e case.pc_rhs]] in
        (re, nG, bs, rhs)
*)
     | {ppat_desc = Ppat_any; _} ->
        error ~loc "Universal wildcard must be the last pattern."
     | {ppat_loc = loc; _} ->
        error ~loc "Regular expression pattern should be a string.")
  in
  let cases, default_rhs =
    (match List.rev cases with
     | {pc_lhs = {ppat_desc = Ppat_any; _}; pc_rhs; pc_guard = None} :: cases ->
        (cases, pc_rhs)
     | {pc_lhs = {ppat_desc = Ppat_var var; _}; pc_rhs; pc_guard = None} ::
       cases ->
        (cases, [%expr let [%p Pat.var var] = _ppx_regexp_v in [%e pc_rhs]])
     | cases ->
        let open Lexing in
        let pos = loc.Location.loc_start in
        let e0 = Exp.constant (Const.string pos.pos_fname) in
        let e1 = Exp.constant (Const.int pos.pos_lnum) in
        let e2 = Exp.constant (Const.int (pos.pos_cnum - pos.pos_bol)) in
        let e = [%expr raise (Match_failure ([%e e0], [%e e1], [%e e2]))] in
        (cases, warn ~loc "A universal case is recommended for %pcre." e))
  in
  let cases = List.rev_map aux cases in
  let res = Exp.array (List.map (fun (re, _, _, _) -> re) cases) in
  let comp = [%expr
    let a = Array.map (fun s -> Re.mark (Re.Perl.re s)) [%e res] in
    let marks = Array.map fst a in
    let re = Re.compile (Re.alt (Array.to_list (Array.map snd a))) in
    (re, marks)
  ] in
  let var = fresh_var () in
  add_binding (Vb.mk (Pat.var {txt = var; loc}) comp);
  let e_comp = Exp.ident {txt = Lident var; loc} in

  let rec handle_cases i offG = function
   | [] -> [%expr assert false]
   | (_, nG, bs, rhs) :: cases ->
      let e_i = Exp.constant (Const.int i) in
      [%expr
        if Re.Mark.test _g (snd [%e e_comp]).([%e e_i]) then
          [%e wrap_group_bindings ~loc rhs offG bs]
        else
          [%e handle_cases (i + 1) (offG + nG) cases]]
  in
  [%expr
    (match Re.exec_opt (fst [%e e_comp]) _ppx_regexp_v with
     | None -> [%e default_rhs]
     | Some _g -> [%e handle_cases 0 0 cases])]

let rewrite_expr mapper e_ext =
  (match e_ext.pexp_desc with
   | Pexp_extension ({txt = "pcre"; _},
                     PStr [{pstr_desc = Pstr_eval (e, _); _}]) ->
      let loc = e.pexp_loc in
      (match e.pexp_desc with
       | Pexp_match (e, cases) ->
          [%expr let _ppx_regexp_v = [%e e] in [%e transform_cases ~loc cases]]
       | Pexp_function (cases) ->
          [%expr fun _ppx_regexp_v -> [%e transform_cases ~loc cases]]
       | _ ->
          error ~loc "[%pcre] only applies to match an function.")
   | _ -> default_mapper.expr mapper e_ext)

let rewrite_structure _mapper sis =
  let sis' =
    default_mapper.structure {default_mapper with expr = rewrite_expr} sis
  in
  (match get_bindings () |> List.rev with
   | [] -> sis'
   | bindings ->
      clear_bindings ();
      let local_sis =
        [%str
          module Ppx_regexp__local = struct
            [%%s [{
              pstr_desc = Pstr_value (Nonrecursive, bindings);
              pstr_loc = Location.none;
            }]]
          end
          open Ppx_regexp__local]
      in
      local_sis @ sis')

let () = Driver.register ~name:"ppx_regexp" ocaml_version
  (fun _config _cookies -> {default_mapper with structure = rewrite_structure})
