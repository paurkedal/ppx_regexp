(* Copyright (C) 2017--2023  Petter A. Urkedal <paurkedal@gmail.com>
 *
 * This library is free software; you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or (at your
 * option) any later version, with the  LGPL-3.0 Linking Exception.
 *
 * This library is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public
 * License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this library.  If not, see <http://www.gnu.org/licenses/>.
 *)

open Ppxlib
open Ast_builder.Default

let error = Location.raise_errorf

let warn ~loc msg e =
  let e_msg = estring ~loc msg in
  let name = {txt = "ocaml.ppwarning"; loc} in
  let payload = PStr [{pstr_desc = Pstr_eval (e_msg, []); pstr_loc = loc}] in
  {e with pexp_attributes = attribute ~loc ~name ~payload :: e.pexp_attributes}

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
       | Capture _ -> error ~loc "Unnamed capture is not allowed for %%pcre."
       | Capture_as (idr, e) ->
          fun (nG, bs) ->
            recurse must_match e (nG + 1, (idr, Some nG, must_match) :: bs)
       | Call _ -> error ~loc "(&...) is not implemented for %%pcre.")
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
            (Printf.sprintf "%s{%d,%s}" (recurse p_atom e) i j_str)
       | Nongreedy e -> recurse p_suffix e ^ "?"
       | Capture _ -> error ~loc "Unnamed capture is not allowed for %%pcre."
       | Capture_as (_, e) -> "(" ^ recurse p_alt e ^ ")"
       | Call _ -> error ~loc "(&...) is not implemented for %%pcre.")
    in
    (function
     | {Location.txt = Capture_as (_, e); _} ->
        recurse 0 e
     | e ->
        recurse 0 e)
end

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
  let loc = Location.none in
  (estring ~loc re_str, bs, nG)

let rec wrap_group_bindings ~loc rhs offG = function
 | [] -> rhs
 | (varG, iG, mustG) :: bs ->
    let eG = match iG with
     | None ->
        [%expr Re.Group.get _g 0]
     | Some iG ->
        [%expr Re.Group.get _g [%e eint ~loc (offG + iG + 1)]]
    in
    let eG =
      if mustG then eG else
      [%expr try Some [%e eG] with Not_found -> None]
    in
    [%expr
      let [%p ppat_var ~loc varG] = [%e eG] in
      [%e wrap_group_bindings ~loc rhs offG bs]]

let rec separate_defaults acc = function
  | [] -> List.rev acc, []
  | ({ pc_lhs = { ppat_desc = Ppat_any; _ }; _ } as case) :: rest -> acc, case :: rest
  | ({ pc_lhs = { ppat_desc = Ppat_var _; _ }; _ } as case) :: rest -> acc, case :: rest
  | case :: rest -> separate_defaults (case :: acc) rest

let make_default_rhs ~loc = function
  | [] ->
    let open Lexing in
    let pos = loc.Location.loc_start in
    let e0 = estring ~loc pos.pos_fname in
    let e1 = eint ~loc pos.pos_lnum in
    let e2 = eint ~loc (pos.pos_cnum - pos.pos_bol) in
    let e = [%expr raise (Match_failure ([%e e0], [%e e1], [%e e2]))] in
    warn ~loc "A universal case is recommended." e
  | default_cases ->
    let transformed =
      List.map
        (fun case ->
          match case.pc_lhs.ppat_desc with
          | Ppat_var var ->
            {
              case with
              pc_lhs = ppat_any ~loc;
              pc_rhs =
                [%expr
                  let [%p ppat_var ~loc var] = _ppx_regexp_v in
                  [%e case.pc_rhs]];
            }
          | _ -> case)
        default_cases
    in
    match transformed with
    | [{ pc_lhs = { ppat_desc = Ppat_any; _ }; pc_guard = None; pc_rhs; _ }] ->
        pc_rhs
    | _ ->
        pexp_match ~loc [%expr _ppx_regexp_v] transformed

let transform_cases ~loc cases =
  let aux case =
    Ast_pattern.(parse (pstring __'))
      loc case.pc_lhs
      begin
        fun { txt = re_src; loc = { loc_start; loc_end; _ } } ->
          let re_offset = (loc_end.pos_cnum - loc_start.pos_cnum - String.length re_src) / 2 in
          let pos = { loc_start with pos_cnum = loc_start.pos_cnum + re_offset; pos_lnum = loc_end.pos_lnum } in
          let re, bs, nG = extract_bindings ~pos re_src in
          re, nG, bs, case.pc_rhs, case.pc_guard
      end
  in
  let group_by_pattern cases =
    List.fold_left
      begin
        fun acc (re, nG, bs, rhs, guard) ->
          let found, groups =
            List.fold_left
              begin
                fun (found, acc_groups) (re', cases) ->
                  if found then found, (re', cases) :: acc_groups
                  else if re = re' then true, (re', (nG, bs, rhs, guard) :: cases) :: acc_groups
                  else false, (re', cases) :: acc_groups
              end
              (false, []) acc
          in
          if found then groups else (re, [ nG, bs, rhs, guard ]) :: groups
      end
      [] cases
  in

  let compute_offsets l =
    let result, _ =
      List.fold_left
        begin
          fun (acc, offG) (re, case_group) ->
            let nG =
              let n, _, _, _ = List.hd (List.rev case_group) in
              n
            in
            (re, case_group, offG) :: acc, offG + nG
        end
        ([], 0) l
    in
    List.rev result
  in

  let cases, default_cases = separate_defaults [] cases in
  let default_rhs = make_default_rhs ~loc default_cases in
  let processed_cases = List.map aux cases |> group_by_pattern |> compute_offsets in

  let res = pexp_array ~loc @@ List.map (fun (re, _, _) -> re) processed_cases in

  let comp =
    [%expr
      let a = Array.map (fun s -> Re.mark (Re.Perl.re s)) [%e res] in
      let marks = Array.map fst a in
      let re = Re.compile (Re.alt (Array.to_list (Array.map snd a))) in
      re, marks]
  in

  let var = fresh_var () in
  let re_binding = value_binding ~loc ~pat:(ppat_var ~loc { txt = var; loc }) ~expr:comp in
  let e_comp = pexp_ident ~loc { txt = Lident var; loc } in

  let case_handlers =
    List.mapi
      begin
        fun i (_, case_group, offG) ->
          let handler_name = Printf.sprintf "_case_%d" i in
          let handler_body =
            let rec mk_guard_chains = function
              | [] -> [%expr None]
              | (_, bs, rhs, guard) :: rest ->
                let bs = List.rev bs in
                begin
                  match guard with
                  | None -> [%expr Some [%e wrap_group_bindings ~loc rhs offG bs]]
                  | Some guard_expr ->
                    let guarded = [%expr if [%e guard_expr] then Some [%e rhs] else [%e mk_guard_chains rest]] in
                    wrap_group_bindings ~loc guarded offG bs
                end
            in
            [%expr fun _g -> [%e mk_guard_chains (List.rev case_group)]]
          in
          handler_name, handler_body
      end
  in

  let mk_checks cases_with_offsets =
    let indexed = List.mapi (fun i x -> i, x) cases_with_offsets in
    List.fold_right
      begin
        fun (i, _) acc ->
          let handler_name = Printf.sprintf "_case_%d" i in
          [%expr
            if Re.Mark.test _g (snd [%e e_comp]).([%e eint ~loc i]) then [%e pexp_ident ~loc { txt = Lident handler_name; loc }] _g
            else [%e acc]]
      end
      indexed [%expr None]
  in

  let handlers = case_handlers processed_cases in
  let dispatchers = mk_checks processed_cases in

  let match_expr =
    [%expr
      match Re.exec_opt (fst [%e e_comp]) _ppx_regexp_v with
      | None -> [%e default_rhs]
      | Some _g ->
        [%e
          List.fold_left
            begin
              fun acc (name, body) ->
                [%expr
                  let [%p ppat_var ~loc { txt = name; loc }] = [%e body] in
                  [%e acc]]
            end
            [%expr match [%e dispatchers] with Some result -> result | None -> [%e default_rhs]]
            handlers]]
  in
  match_expr, re_binding

let transformation = object
  inherit [value_binding list] Ast_traverse.fold_map as super

  method! expression e_ext acc =
    let e_ext, acc = super#expression e_ext acc in
    (match e_ext.pexp_desc with
     | Pexp_extension
         ({txt = "pcre"; _}, PStr [{pstr_desc = Pstr_eval (e, _); _}]) ->
        let loc = e.pexp_loc in
        (match e.pexp_desc with
         | Pexp_match (e, cases) ->
            let cases, binding = transform_cases ~loc cases in
            ([%expr let _ppx_regexp_v = [%e e] in [%e cases]], binding :: acc)
         | Pexp_function (cases) ->
            let cases, binding = transform_cases ~loc cases in
            ([%expr fun _ppx_regexp_v -> [%e cases]], binding :: acc)
         | _ ->
            error ~loc "[%%pcre] only applies to match an function.")
     | _ -> (e_ext, acc))
end

let impl str =
  let str, rev_bindings = transformation#structure str [] in
  if rev_bindings = [] then str else
  let re_str =
    let loc = Location.none in
    [%str open (struct [%%i pstr_value ~loc Nonrecursive rev_bindings] end)]
  in
  re_str @ str

let () = Driver.register_transformation ~impl "ppx_regexp"
