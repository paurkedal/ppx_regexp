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
       | Call _ -> fun (nG, bs) -> (nG + 1, bs))
    in
    (function
     | {Location.txt = Capture_as (idr, e); _} ->
        recurse true e (1, [idr, Some 0, true])
     | e ->
        recurse true e (0, []))

  let rec to_re_expr ~loc ~in_let (e : _ Location.loc) =
    let open Ast_builder.Default in
    match e.Location.txt with
    | Code s ->
        [%expr Re.Perl.re [%e estring ~loc s]]
    | Seq es ->
        let exprs = List.map (to_re_expr ~loc ~in_let) es in
        [%expr Re.seq [%e elist ~loc exprs]]
    | Alt es ->
        let exprs = List.map (to_re_expr ~loc ~in_let) es in
        [%expr Re.alt [%e elist ~loc exprs]]
    | Opt e ->
        [%expr Re.opt [%e to_re_expr ~loc ~in_let e]]
    | Repeat ({Location.txt = (i, j_opt); _}, e) ->
        let e_i = eint ~loc i in
        let e_j = match j_opt with
          | None -> [%expr None]
          | Some j -> [%expr Some [%e eint ~loc j]]
        in
        [%expr Re.repn [%e to_re_expr ~loc ~in_let e] [%e e_i] [%e e_j]]
    | Nongreedy e ->
        [%expr Re.non_greedy [%e to_re_expr ~loc ~in_let e]]
    | Capture e ->
        [%expr Re.group [%e to_re_expr ~loc ~in_let e]]
    | Capture_as (_, e) ->
        [%expr Re.group [%e to_re_expr ~loc ~in_let e]]
    | Call lid ->
        if in_let then pexp_ident ~loc lid else
        [%expr Re.group [%e pexp_ident ~loc lid]]

  let rec squash_codes (e : _ Location.loc) : _ Location.loc =
    let open Location in
    let rec combine (nodes : _ Location.loc list) =
      match nodes with
      | [] -> []
      | {Location.txt = Code s1; loc = loc1} :: {Location.txt = Code s2; loc = loc2} :: rest ->
          let combined_loc =
            if loc1 = Location.none || loc2 = Location.none then Location.none
            else Location.{
              loc_start = loc1.loc_start;
              loc_end = loc2.loc_end;
              loc_ghost = false;
            }
          in
          combine ({Location.txt = Code (s1 ^ s2); loc = combined_loc} :: rest)
      | node :: rest -> node :: combine rest
    in
    match e.txt with
    | Code _ -> e
    | Seq es ->
        let es = List.map squash_codes es in
        {e with txt = Seq (combine es)}
    | Alt es ->
        let es = List.map squash_codes es in
        {e with txt = Alt es}
    | Opt e' -> {e with txt = Opt (squash_codes e')}
    | Repeat (range, e') -> {e with txt = Repeat (range, squash_codes e')}
    | Nongreedy e' -> {e with txt = Nongreedy (squash_codes e')}
    | Capture e' -> {e with txt = Capture (squash_codes e')}
    | Capture_as (name, e') -> {e with txt = Capture_as (name, squash_codes e')}
    | Call _ -> e
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
  let r = Regexp.(squash_codes @@ parse_exn ~pos s) in
  let nG, bs = Regexp.bindings r in
  let loc = Location.none in
  let re_expr = Regexp.to_re_expr ~loc ~in_let:false r in
  (re_expr, bs, nG)

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

let transform_let =
  List.map
    begin
      fun vb ->
        match vb.pvb_pat.ppat_desc, vb.pvb_expr.pexp_desc with
        | Ppat_var { txt = _; loc }, Pexp_constant (Pconst_string (value, _, _)) ->
          let parsed = Regexp.(squash_codes @@ parse_exn value) in
          let re_expr = Regexp.to_re_expr ~loc ~in_let:true parsed in
          let expr = [%expr [%e re_expr]] in
          { vb with pvb_expr = expr }
        | _ -> vb
    end

let transform_cases ~loc cases =
  let aux case =
    if case.pc_guard <> None then
      error ~loc "Guards are not implemented for match%%pcre."
    else
    Ast_pattern.(parse (pstring __')) loc case.pc_lhs
      begin fun {txt = re_src; loc = {loc_start; loc_end; _}} ->
        let re_offset =
          (loc_end.pos_cnum - loc_start.pos_cnum - String.length re_src) / 2
        in
        let pos = {loc_start with pos_cnum = loc_start.pos_cnum + re_offset} in
        let re, bs, nG = extract_bindings ~pos re_src in
        (re, nG, bs, case.pc_rhs)
      end
  in
  let cases, default_rhs =
    (match List.rev (*_map rewrite_case*) cases with
     | {pc_lhs = {ppat_desc = Ppat_any; _}; pc_rhs; pc_guard = None} :: cases ->
        (cases, pc_rhs)
     | {pc_lhs = {ppat_desc = Ppat_var var; _}; pc_rhs; pc_guard = None} ::
       cases ->
        let rhs =
          [%expr let [%p ppat_var ~loc var] = _ppx_regexp_v in [%e pc_rhs]] in
        (cases, rhs)
     | cases ->
        let open Lexing in
        let pos = loc.Location.loc_start in
        let e0 = estring ~loc pos.pos_fname in
        let e1 = eint ~loc pos.pos_lnum in
        let e2 = eint ~loc (pos.pos_cnum - pos.pos_bol) in
        let e = [%expr raise (Match_failure ([%e e0], [%e e1], [%e e2]))] in
        (cases, warn ~loc "A universal case is recommended for %pcre." e))
  in
  let cases = List.rev_map aux cases in
  let res = pexp_array ~loc (List.map (fun (re, _, _, _) -> re) cases) in
  let comp = [%expr
    let a = Array.map (fun re -> Re.mark re) [%e res] in
    let marks = Array.map fst a in
    let re = Re.compile (Re.alt (Array.to_list (Array.map snd a))) in
    (re, marks)
  ] in
  let var = fresh_var () in
  let re_binding =
    value_binding ~loc ~pat:(ppat_var ~loc {txt = var; loc}) ~expr:comp
  in
  let e_comp = pexp_ident ~loc {txt = Lident var; loc} in

  let rec handle_cases i offG = function
   | [] -> [%expr assert false]
   | (_, nG, bs, rhs) :: cases ->
      [%expr
        if Re.Mark.test _g (snd [%e e_comp]).([%e eint ~loc i]) then
          [%e wrap_group_bindings ~loc rhs offG bs]
        else
          [%e handle_cases (i + 1) (offG + nG) cases]]
  in
  let cases =
    [%expr
      (match Re.exec_opt (fst [%e e_comp]) _ppx_regexp_v with
       | None -> [%e default_rhs]
       | Some _g -> [%e handle_cases 0 0 cases])]
  in
  (cases, re_binding)

let transformation = object
  inherit [value_binding list * value_binding list] Ast_traverse.fold_map as super

    method! structure_item item (acc, let_acc) =
      match item.pstr_desc with
      (* let%pcre x = {|some regex|}*)
      | Pstr_extension (({ txt = "pcre"; loc }, PStr [ { pstr_desc = Pstr_value (Nonrecursive, vbs); _ } ]), _) ->
        let bindings = transform_let vbs in
        let dummy = {item with pstr_desc = Pstr_eval ([%expr ()], [])} in
        dummy, (acc, bindings @ let_acc)
      | _ -> super#structure_item item (acc, let_acc)

  method! expression e_ext acc =
    let e_ext, (acc, let_acc) = super#expression e_ext acc in
    (match e_ext.pexp_desc with
     | Pexp_extension
         ({txt = "pcre"; _}, PStr [{pstr_desc = Pstr_eval (e, _); _}]) ->
        let loc = e.pexp_loc in
        (match e.pexp_desc with
         | Pexp_match (e, cases) ->
            let cases, binding = transform_cases ~loc cases in
            ([%expr let _ppx_regexp_v = [%e e] in [%e cases]], (binding :: acc, let_acc))
         | Pexp_function (cases) ->
            let cases, binding = transform_cases ~loc cases in
            ([%expr fun _ppx_regexp_v -> [%e cases]], (binding :: acc, let_acc))
         | _ ->
            error ~loc "[%%pcre] only applies to match an function.")
     | _ -> (e_ext, (acc, let_acc)))
end

let impl str =
  let str, (rev_bindings, let_bindings) = transformation#structure str ([], []) in
  if rev_bindings = [] then str else
    let loc = Location.none in
    let all_bindings = List.rev let_bindings @ rev_bindings in
    let struct_items =
      List.fold_left (fun acc binding ->
        acc @ [%str let [%p binding.pvb_pat] = [%e binding.pvb_expr]]
      ) [] all_bindings
    in
    let mod_expr = pmod_structure ~loc struct_items in
    [%str open [%m mod_expr]] @ str

let () = Driver.register_transformation ~impl "ppx_regexp"
