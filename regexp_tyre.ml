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

let fresh_var =
  let c = ref 0 in
  fun () -> incr c; Printf.sprintf "_ppx_regexp_%d" !c

module Tyre = struct

  let mk ~loc s =
    A.Exp.ident ~loc @@ Loc.mkloc Longident.(Ldot (Lident "Tyre", s)) loc

  let mkf ~loc s l =
    A.Exp.apply ~loc (mk ~loc s) l
  
  let conv ~loc to_ from_ t =
    mkf ~loc "conv" [Nolabel, to_ ; Nolabel, from_ ; Nolabel, t]

  let bin ~loc s a b = mkf ~loc s [Nolabel, a ; Nolabel, b]

end

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
  | [] -> assert false
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
    | _, _ -> assert false
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

(** Sequences *)

let flatten_seq =
  let rec f = function
    | Regexp.Seq l -> flatten l
    | x -> [x]
  and flatten l = List.flatten @@ List.map f l
  in
  flatten

type ('a, 'b) capture =
   | No
   | Named of 'a
   | Unnamed of 'b
let rec capture =
  let open Regexp in function
  | Re _ -> No
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
  | Repeat (_,_,t) -> capture t
  | Capture _ -> Unnamed ()
  | Capture_as (s,_) -> Named s
  | Call _ -> Unnamed ()
let capture_singleton = function
  | No -> No
  | Unnamed () -> Unnamed 1
  | Named s -> Named [s]

let seq_to_expr ~loc l =
  let rec f = function
    | [] -> assert false
    | [ capture, e ] -> capture_singleton capture, e
    | (capture, e) :: exprs ->
       let captures, exprs = f exprs in
      let captures, (<&>) = match capture, captures with
        | c, No -> capture_singleton c, Tyre.bin ~loc "suffix"
        | No, c -> c, Tyre.bin ~loc "prefix"
        | Unnamed (), Unnamed i -> Unnamed (i+1), Tyre.bin ~loc "seq"
        | Named s, Named l -> Named (s :: l), Tyre.bin ~loc "seq"
        | Unnamed _, Named _ | Named _, Unnamed _ -> assert false
      in
      captures, e <&> exprs
  in
  let seq_capture, seq_expr = f l in
  match seq_capture with
  | No -> failwith "Meh."
  | Unnamed i -> make_conv_tuple ~loc i seq_expr
  | Named l -> make_conv_object ~loc l seq_expr

(** Put everything together *)

let rec expr_of_regex ~loc t =
  match t with
  | Regexp.Re _ -> failwith "TODO"
  | Seq l ->
    let seq_item re = capture re, expr_of_regex ~loc re in
    seq_to_expr ~loc @@ List.map seq_item l
  | Alt _ -> failwith "TODO"
  | Opt t ->
    Tyre.mkf ~loc "opt" [Nolabel, expr_of_regex ~loc t]
  | Repeat (0, None, t) -> Tyre.mkf ~loc "rep" [Nolabel, expr_of_regex ~loc t]
  | Repeat (_,_,_) -> failwith "TODO"
  | Capture t -> expr_of_regex ~loc t
  | Capture_as (_, t) -> expr_of_regex ~loc t
  | Call lid -> A.Exp.ident lid
