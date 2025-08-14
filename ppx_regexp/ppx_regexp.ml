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

let transformation ctx =
  object (self)
    inherit [value_binding list] Ast_traverse.fold_map as super

    method! structure_item item acc =
      match item.pstr_desc with
      (* let%mik/%pcre x = {|some regex|}*)
      | Pstr_extension (({ txt = ("pcre" | "mikmatch") as ext; _ }, PStr [ { pstr_desc = Pstr_value (rec_flag, vbs); _ } ]), _) ->
        let mode = if ext = "pcre" then `Pcre else `Mik in
        let bindings = Transformations.transform_let ~mode ~ctx vbs in
        let new_item = { item with pstr_desc = Pstr_value (rec_flag, bindings) } in
        new_item, acc
      (* let x = expression (which might contain %mik/%pcre) *)
      | Pstr_value (rec_flag, vbs) ->
        let processed_vbs, collected_bindings =
          List.fold_left
            (fun (vbs_acc, bindings_acc) vb ->
              match vb.pvb_expr.pexp_desc with
              | Pexp_extension ({ txt = ("pcre" | "mikmatch") as ext; _ }, PStr [ { pstr_desc = Pstr_eval (expr, _); _ } ])
                when match expr.pexp_desc with Pexp_constant (Pconst_string _) -> true | _ -> false ->
                let mode = if ext = "pcre" then `Pcre else `Mik in
                let new_vb = { vb with pvb_expr = expr } in
                let transformed = Transformations.transform_let ~mode ~ctx [ new_vb ] in
                List.hd transformed :: vbs_acc, bindings_acc
              | _ ->
                let new_expr, new_bindings = self#expression vb.pvb_expr bindings_acc in
                let new_vb = { vb with pvb_expr = new_expr } in
                new_vb :: vbs_acc, new_bindings)
            ([], acc) vbs
        in
        let new_item = { item with pstr_desc = Pstr_value (rec_flag, List.rev processed_vbs) } in
        new_item, collected_bindings
      | _ -> super#structure_item item acc

    method! expression e_ext acc =
      let e_ext, acc = super#expression e_ext acc in
      let make_transformations ~mode ~opts ~loc = function
        | Pexp_function cases ->
          let cases, binding = Transformations.transform_cases ~mode ~opts ~loc ~ctx cases in
          [%expr fun _ppx_regexp_v -> [%e cases]], binding @ acc
        | Pexp_match (e, cases) ->
          let cases, binding = Transformations.transform_cases ~mode ~opts ~loc ~ctx cases in
          ( [%expr
              let _ppx_regexp_v = [%e e] in
              [%e cases]],
            binding @ acc )
        | _ -> Util.error ~loc "[%%pcre] and [%%mik] only apply to match, function and global let declarations of strings."
      in
      match e_ext.pexp_desc with
      (* match%mikmatch/match%pcre and function%mikmatch/function%pcre, mikmatch anchored *)
      | Pexp_extension ({ txt = ("pcre" | "mikmatch" | "pcre_i" | "mikmatch_i") as ext; _ }, PStr [ { pstr_desc = Pstr_eval (e, _); _ } ])
        ->
        let mode, opts = if String.starts_with ~prefix:"pcre" ext then `Pcre, [] else `Mik, Util.mikmatch_default_opts in
        let opts = if String.ends_with ~suffix:"_i" ext then `Caseless :: opts else opts in
        let loc = e.pexp_loc in
        make_transformations ~mode ~opts ~loc e.pexp_desc
      (* match smth with | {%mikmatch|some regex|} -> ...*)
      | Pexp_match (matched_expr, cases) ->
        let has_ext_case =
          List.exists
            begin
              fun case ->
                match case.pc_lhs.ppat_desc with
                | Ppat_extension ({ txt = "pcre" | "mikmatch" | "pcre_i" | "mikmatch_i"; _ }, _) -> true
                | _ -> false
            end
            cases
        in
        if has_ext_case then Transformations.transform_mixed_match ~loc:e_ext.pexp_loc ~ctx ~matched_expr cases acc else e_ext, acc
      | Pexp_function cases ->
        let has_ext_case =
          List.exists
            begin
              fun case ->
                match case.pc_lhs.ppat_desc with
                | Ppat_extension ({ txt = "pcre" | "mikmatch" | "pcre_i" | "pcres_i" | "mikmatch_i"; _ }, _) -> true
                | _ -> false
            end
            cases
        in
        if has_ext_case then Transformations.transform_mixed_match ~loc:e_ext.pexp_loc ~ctx cases acc else e_ext, acc
      | _ -> e_ext, acc
  end

let dispatch_function_binding ~loc =
  let open Ppxlib in
  let open Ast_builder.Default in
  value_binding ~loc
    ~pat:(ppat_var ~loc { txt = "__ppx_regexp_dispatch"; loc })
    ~expr:
      [%expr
        fun marks handlers _g ->
          let rec loop i =
            if i >= Array.length marks then None
            else if Re.Mark.test _g marks.(i) then (match handlers.(i) _g with Some result -> Some result | None -> loop (i + 1))
            else loop (i + 1)
          in
          loop 0]

let impl str =
  let ctx = Util.Ctx.empty () in
  let str, rev_bindings = (transformation ctx)#structure str [] in
  if rev_bindings = [] then str
  else (
    let re_str =
      let loc = Location.none in
      [%str
        open struct
          [%%i pstr_value ~loc Nonrecursive [ dispatch_function_binding ~loc ]]
          [%%i pstr_value ~loc Nonrecursive rev_bindings]
        end]
    in
    re_str @ str)

let () = Driver.register_transformation ~impl "ppx_regexp"
