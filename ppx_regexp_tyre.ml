(* Copyright (C) 2018  Gabriel Radanne <drupyog@zoho.com>
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
module AC = Ast_convenience_404

module A = Ast_helper
module Loc = Location

let internal_error ~loc = Loc.raise_errorf ~loc "Internal error@."

let fresh_var =
  let c = ref 0 in
  fun () -> incr c; Printf.sprintf "_ppx_regexp_%d" !c

let nolabel x = (Asttypes.Nolabel, x)

module Tyre = struct

  let mk ~loc s = AC.evar ~loc ("Tyre."^s)

  let mkf ~loc s l =
    A.Exp.apply ~loc (mk ~loc s) l

  let conv ~loc to_ from_ t =
    mkf ~loc "conv" [Nolabel, to_ ; Nolabel, from_ ; Nolabel, t]

  let bin ~loc s a b = mkf ~loc s [Nolabel, a; Nolabel, b]

end

module Re = struct

  let mk ~loc s = AC.evar ~loc ("Re."^s)

  let mkf ~loc s l =
    A.Exp.apply ~loc (mk ~loc s) l
      
  let mkfl ~loc s l = mkf ~loc s [Nolabel, AC.list ~loc l]

end

(** Utilities for captures *)

type ('a, 'b) capture =
   | No
   | Named of 'a
   | Unnamed of 'b

let rec capture e =
  let open Regexp in
  match e.Loc.txt with
  | Code _ -> No
  | Seq l ->
    if List.for_all (fun x -> capture x = No) l then
      No
    else
      Unnamed ()
  | Alt l ->
    if List.exists (fun x -> capture x = No) l then
      No
    else
      Unnamed ()
  | Opt t -> capture t
  | Repeat (_,t) -> capture t
  | Capture _ -> Unnamed ()
  | Capture_as (s,_) -> Named s.Loc.txt
  | Call _ -> Unnamed ()

let capture_singleton = function
  | No -> No
  | Unnamed () -> Unnamed 1
  | Named s -> Named [s]

(** Simplification of regexps *)

let flatten_seq =
  let rec f e =
    match e.Loc.txt with
    | Regexp.Seq l -> flatten l
    | _ -> [e]
  and flatten l = List.flatten @@ List.map f l
  in
  flatten

let flatten_alt =
  let rec f e =
    match e.Loc.txt with
    | Regexp.Alt l -> flatten l
    | _ -> [e]
  and flatten l = List.flatten @@ List.map f l
  in
  flatten

let extract_re_list ~loc l =
  let is_re = function {Loc.txt = Regexp.Code _; _} -> true | _ -> false in
  let get = function {Loc.txt = Regexp.Code r; _} -> r | _ -> internal_error ~loc in
  if List.for_all is_re l then Some (List.map get l) else None

let rec collapse_ungrouped (t : string Regexp.t) =
  let loc = t.Loc.loc in
  match t.Loc.txt with
  | Regexp.Code e ->
    let f = AC.evar ~loc "Re.Perl.re" in
    let s = A.Exp.constant ~loc (A.Const.string e) in
    Loc.mkloc (Regexp.Code (A.Exp.apply ~loc f [Nolabel, s])) loc
  | Call lid ->
    Loc.mkloc (Regexp.Call lid) loc
  | Capture t ->
    Loc.mkloc (Regexp.Capture (collapse_ungrouped t)) t.Loc.loc
  | Capture_as (s, t) ->
    Loc.mkloc (Regexp.Capture_as (s, collapse_ungrouped t)) t.Loc.loc
  | Seq l ->
    let l = flatten_seq @@ List.map collapse_ungrouped l in
    let e = match extract_re_list ~loc l with
      | Some r -> Regexp.Code (Re.mkfl "seq" ~loc r)
      | None -> Regexp.Seq l
    in
    Loc.mkloc e t.Loc.loc
  | Alt l ->
    let l = flatten_alt @@ List.map collapse_ungrouped l in
    let e = match extract_re_list ~loc l with
      | Some r -> Regexp.Code (Re.mkfl "alt" ~loc r)
      | None -> Regexp.Alt l
    in
    Loc.mkloc e t.Loc.loc
  | Opt t ->
    let e = match collapse_ungrouped t with
      | {Loc.txt = Regexp.Code r; _} ->
          Regexp.Code (Re.mkf ~loc "opt" [nolabel r])
      | t -> Opt t
    in
    Loc.mkloc e t.Loc.loc
  | Repeat ({Loc.txt = (i, j); _} as ij, t) ->
    let e = match collapse_ungrouped t with
      | {Loc.txt = Regexp.Code r; _} ->
        let i = A.Exp.constant (A.Const.int i) in
        let j =
          match j with
          | None -> AC.constr "None" []
          | Some j -> AC.constr "Some" [A.Exp.constant (A.Const.int j)]
        in
        Regexp.Code (Re.mkf ~loc "repn" [nolabel r; nolabel i; nolabel j])
      | t -> Repeat (ij, t)
    in
    Loc.mkloc e t.Loc.loc

let simplify = collapse_ungrouped

(** Converters to/from nested tuples *)

let rec make_nested_tuple_pat ~loc n =
  let v = fresh_var () in
  if n = 1 then
    [v], AC.pvar ~loc v
  else
    let vars, pat = make_nested_tuple_pat ~loc (n-1) in
    (v :: vars), A.Pat.tuple ~loc [AC.pvar ~loc v;pat]
let rec make_nested_tuple_expr ~loc exprs =
  match exprs with
  | [] -> internal_error ~loc
  | [e] -> e
  | e :: exprs ->
    let tuples = make_nested_tuple_expr ~loc exprs in
    A.Exp.tuple ~loc [e; tuples]
let make_object_expr ~loc expr meths =
  let rec f expr meths = match expr, meths with
    | [], [] -> []
    | expr :: exprs, meth :: meths ->
      let decls = f exprs meths in
      let decl =
        A.Cf.method_ ~loc (Loc.mkloc meth loc)
          Public
          (Cfk_concrete (Fresh, expr))
      in
      decl :: decls
    | _, _ -> internal_error ~loc
  in
  A.Exp.object_ ~loc (A.Cstr.mk (A.Pat.any ~loc ()) @@ f expr meths)

let make_conv_of_nested_tuple ~loc ~make_pat ~make_expr ~n tyre_expr =
  let fun_to =
    let vars, tuple_pat = make_nested_tuple_pat ~loc n in
    let lids = List.map (AC.evar ~loc) vars in
    let expr = make_expr ~loc lids in
    A.Exp.fun_ ~loc Nolabel None tuple_pat expr
  in
  let fun_from =
    let obj_pat, subexprs = make_pat ~loc () in
    let expr = make_nested_tuple_expr ~loc subexprs in
    A.Exp.fun_ ~loc Nolabel None obj_pat expr
  in
  Tyre.conv ~loc fun_to fun_from tyre_expr

let make_conv_object ~loc meths tyre_expr =
  let n = List.length meths in
  let make_expr ~loc lids =
    make_object_expr ~loc lids meths
  in
  let make_pat ~loc () =
    let obj_var = fresh_var () in
    let obj = AC.evar ~loc obj_var in
    let obj_pat = AC.pvar ~loc obj_var in
    let methsends = List.map (fun m -> A.Exp.send ~loc obj m) meths in
    obj_pat, methsends
  in
  make_conv_of_nested_tuple ~loc ~n ~make_expr ~make_pat tyre_expr

let make_conv_tuple ~loc n tyre_expr =
  let make_expr ~loc l = A.Exp.tuple ~loc l in
  let make_pat ~loc () =
    let ids = List.init n (fun _ -> fresh_var ()) in
    let plids = List.map (AC.pvar ~loc) ids in
    let elids = List.map (AC.evar ~loc) ids in
    let ptuple = A.Pat.tuple ~loc plids in
    ptuple, elids
  in
  make_conv_of_nested_tuple ~loc ~n ~make_expr ~make_pat tyre_expr

(** Converters to/from nested either types *)

let ppoly s ~loc x = A.Pat.(variant ~loc s (Some x))
let epoly s ~loc x = A.Exp.(variant ~loc s (Some x))

let eleft = epoly "Left"
let eright = epoly "Right"
let pleft = ppoly "Left"
let pright = ppoly "Right"

let rec make_match_from_nested ~loc mk_exprs matched =
  match mk_exprs with
  | [] -> internal_error ~loc
  | [ mk_expr ] -> mk_expr matched
  | mk_expr :: mk_exprs ->
    let left_id = fresh_var () in
    let right_id = fresh_var () in
    let right_expr = make_match_from_nested ~loc mk_exprs (AC.evar right_id) in
    A.Exp.(match_ ~loc matched [
        case (pleft ~loc @@ AC.pvar left_id) (mk_expr @@ AC.evar ~loc left_id) ;
        case (pright ~loc @@ AC.pvar right_id) right_expr ;
      ])

let make_match_to_nested ~loc mk_pats matched =
  let length = List.length mk_pats in
  let make_nested_either_constr ~loc n expr =
    let rec nested_rights ~loc n expr =
      if n = 0 then expr
      else eright ~loc (nested_rights ~loc (n-1) expr)
    in
    if n = length - 1 then nested_rights ~loc n expr
    else nested_rights ~loc n (eleft ~loc expr)
  in
  let make_case n mk_pat =
    let id = fresh_var () in
    A.Exp.case
      (mk_pat @@ AC.pvar ~loc id)
      (make_nested_either_constr ~loc n @@ AC.evar ~loc id)
  in
  A.Exp.match_ ~loc matched @@ List.mapi make_case mk_pats 

let make_conv_sum ~loc captures tyre_expr =
  let name_from_capture i = function 
    | No ->
      Loc.raise_errorf ~loc
        "All alternatives branches must have a capturing group."
    | Unnamed _ -> "Alt"^string_of_int i
    | Named s -> s
  in
  let branchnames = List.mapi name_from_capture captures in
  let id = fresh_var () in
  let fun_to =
    let expr_branchs = List.map (epoly ~loc) branchnames in
    let expr =  make_match_from_nested ~loc expr_branchs (AC.evar ~loc id) in
    A.Exp.fun_ ~loc Nolabel None (AC.pvar ~loc id) expr
  in
  let fun_from =
    let pat_branchs = List.map (ppoly ~loc) branchnames in 
    let expr =  make_match_to_nested ~loc pat_branchs (AC.evar ~loc id) in
    A.Exp.fun_ ~loc Nolabel None (AC.pvar ~loc id) expr
  in
  Tyre.conv ~loc fun_to fun_from tyre_expr
  
(** Alternatives *)

let rec alt_to_expr ~loc = function
  | [] -> internal_error ~loc
  | [ e ] -> e
  | (e) :: exprs ->
    let exprs = alt_to_expr ~loc exprs in
    Tyre.bin ~loc "alt" e exprs

let alt_to_conv ~loc captures exprs =
  let alt_expr = alt_to_expr ~loc exprs in
  make_conv_sum ~loc captures alt_expr

(** Sequences *)

let rec seq_to_expr ~loc = function
  | [] -> internal_error ~loc
  | [ capture, e ] -> capture_singleton capture, e
  | (capture, e) :: exprs ->
    let captures, exprs = seq_to_expr ~loc exprs in
    let captures, (<&>) = match capture, captures with
      | c, No -> capture_singleton c, Tyre.bin ~loc "suffix"
      | No, c -> c, Tyre.bin ~loc "prefix"
      | Unnamed (), Unnamed i -> Unnamed (i+1), Tyre.bin ~loc "seq"
      | Named s, Named l -> Named (s :: l), Tyre.bin ~loc "seq"
      | Unnamed _, Named _ | Named _, Unnamed _ ->
        Loc.raise_errorf ~loc
          "The same sequence must not mix unnamed and named capture groups@."
    in
    captures, e <&> exprs

let seq_to_conv ~loc l =
  let seq_capture, seq_expr = seq_to_expr ~loc l in
  match seq_capture with
  | No ->
    (* This case should not happen: If simplification was run,
       sequence of ungrouped regex would have been collapsed. *)
    internal_error ~loc
  | Unnamed 0 | Named [] ->
    internal_error ~loc (* No. *)
  | Unnamed 1 | Named [_] ->
    seq_expr
  | Unnamed i -> make_conv_tuple ~loc i seq_expr
  | Named l -> make_conv_object ~loc l seq_expr

(** Put everything together *)

let rec expr_of_regex (t : _ Regexp.t) =
  let loc = t.Loc.loc in
  match t.Loc.txt with
  | Regexp.Code r ->
    Tyre.mkf ~loc "regex" [nolabel r]
  | Seq l ->
    let seq_item re = capture re, expr_of_regex re in
    seq_to_conv ~loc @@ List.map seq_item l
  | Alt l ->
    let exprs = List.map expr_of_regex l in
    let captures = List.map capture l in
    alt_to_conv ~loc captures exprs
  | Opt t ->
    Tyre.mkf ~loc "opt" [Nolabel, expr_of_regex t]
  | Repeat ({Loc.txt = (0, None); _}, t) ->
    Tyre.mkf ~loc "rep" [Nolabel, expr_of_regex t]
  | Repeat ({Loc.txt = (1, None); _}, t) ->
    Tyre.mkf ~loc "rep1" [Nolabel, expr_of_regex t]
  | Repeat (_,_) -> failwith "TODO"
  | Capture t -> expr_of_regex t
  | Capture_as (_, t) -> expr_of_regex t
  | Call lid -> A.Exp.ident lid

let expr_of_string ~pos s =
  match Regexp.parse ~pos s with
  | Ok re -> expr_of_regex @@ simplify re
  | Error { loc; msg } ->
    Loc.raise_errorf ~loc "%s@." msg

open Ast_mapper

let adjust_position ~loc delim =
  let (+~) pos i = Lexing.{pos with pos_cnum = pos.pos_cnum + i } in
  match delim with
  | None -> loc.Loc.loc_start +~ 1
  | Some s -> loc.Loc.loc_start +~ (String.length s + 2)

let expr mapper e_ext =
  let open Parsetree in
  match e_ext.pexp_desc with
  | Pexp_extension ({txt = "tyre"; _},
                    PStr [{pstr_desc = Pstr_eval (e, _); _}]) ->
    let loc = e.pexp_loc in
    (match e.pexp_desc with
     | Pexp_constant (Pconst_string (s, delim)) ->
       let pos = adjust_position ~loc delim in
       expr_of_string ~pos s
     | _ ->
       Loc.raise_errorf ~loc "[%%tyre] is only allowed on constant strings and match expressions.")
  | _ -> default_mapper.expr mapper e_ext

let () =
  Driver.register
    ~name:"ppx_regexp.tyre" ocaml_version
    (fun _config _cookies -> {default_mapper with expr})
