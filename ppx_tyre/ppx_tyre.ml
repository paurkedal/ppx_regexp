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

let mk_gen s = 
  let c = ref 0 in
  fun () -> incr c; Printf.sprintf "%s%d" s !c

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
    let cs = List.map capture l in
    let l = List.filter (function No -> false | _ -> true) cs in
    begin match l with
      | [] -> No
      | [ c ] -> c
      | _ -> Unnamed ()
    end
  | Alt l ->
    if List.exists (fun x -> capture x = No) l then
      No
    else
      Unnamed ()
  | Opt t -> capture t
  | Repeat (_,t) -> capture t
  | Nongreedy t -> capture t
  | Capture _ -> Unnamed ()
  | Capture_as (s,_) -> Named s
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
  let get =
    function {Loc.txt = Regexp.Code r; _} -> r | _ -> internal_error ~loc in
  if List.for_all is_re l then Some (List.map get l) else None
  
let collapse_ungrouped_seq ~loc l =
  let mkseq = function
    | [] -> []
    | rl -> [Loc.mkloc (Regexp.Code (Re.mkfl "seq" ~loc @@ List.rev rl)) loc]
  in
  let rec aux acc = function
    | [] -> mkseq acc
    | {Loc.txt = Regexp.Code r ; _ } :: l -> aux (r :: acc) l
    | h :: t ->
      mkseq acc @ h :: aux [] t
  in
  match aux [] l with
  | [] -> Regexp.Code (Re.mk ~loc "epsilon")
  | [ x ] -> x.txt
  | l -> Seq l

let rec collapse_ungrouped (t : string Regexp.t) =
  let loc = t.Loc.loc in
  let e : _ Regexp.node = match t.Loc.txt with
    | Regexp.Code e ->
      let f = AC.evar ~loc "Re.Perl.re" in
      let s = A.Exp.constant ~loc (A.Const.string e) in
      Code (A.Exp.apply ~loc f [Nolabel, s])
    | Call lid ->
      Call lid
    | Capture t ->
      Capture (collapse_ungrouped t)
    | Capture_as (s, t) ->
      Capture_as (s, collapse_ungrouped t)
    | Seq l ->
      let l = flatten_seq @@ List.map collapse_ungrouped l in
      collapse_ungrouped_seq ~loc l
    | Alt l ->
      let l = flatten_alt @@ List.map collapse_ungrouped l in
      begin match extract_re_list ~loc l with
        | Some r -> Code (Re.mkfl "alt" ~loc r)
        | None -> Alt l
      end
    | Opt t ->
      begin match collapse_ungrouped t with
        | {Loc.txt = Code r; _} ->
          Code (Re.mkf ~loc "opt" [Nolabel, r])
        | t -> Opt t
      end
    | Repeat ({Loc.txt = (i, j); _} as ij, t) ->
      begin match collapse_ungrouped t with
        | {Loc.txt = Code r; _} ->
          let i = A.Exp.constant (A.Const.int i) in
          let j =
            match j with
            | None -> AC.constr "None" []
            | Some j -> AC.constr "Some" [A.Exp.constant (A.Const.int j)]
          in
          Code (Re.mkf ~loc "repn" [Nolabel, r; Nolabel, i; Nolabel, j])
        | t -> Repeat (ij, t)
      end
    | Nongreedy t ->
      begin match collapse_ungrouped t with
        | {Loc.txt = Code r; _} ->
          Code (Re.mkf ~loc "non_greedy" [Nolabel, r])
        | t -> Nongreedy t
      end
  in
  Loc.mkloc e loc

let simplify = collapse_ungrouped

(** Converters to/from nested tuples *)

let rec make_nested_tuple_pat ~loc ids =
  match ids with
  | [] -> internal_error ~loc
  | [ v ] -> [v], AC.pvar ~loc v
  | v :: ids -> 
    let vars, pat = make_nested_tuple_pat ~loc ids in
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
        A.Cf.method_ ~loc meth
          Public
          (Cfk_concrete (Fresh, expr))
      in
      decl :: decls
    | _, _ -> internal_error ~loc
  in
  A.Exp.object_ ~loc (A.Cstr.mk (A.Pat.any ~loc ()) @@ f expr meths)

let make_conv_of_nested_tuple ~loc ~make_pat ~make_expr ~ids tyre_expr =
  let fun_to =
    let vars, tuple_pat = make_nested_tuple_pat ~loc ids in
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
  let obj_var = "v" in
  let gen = mk_gen obj_var in
  let ids = List.init (List.length meths) (fun _ -> gen ()) in
  let make_expr ~loc lids =
    make_object_expr ~loc lids meths
  in
  let make_pat ~loc () =
    let obj = AC.evar ~loc obj_var in
    let obj_pat = AC.pvar ~loc obj_var in
    let methsends = List.map (fun m -> A.Exp.send ~loc obj m.Loc.txt) meths in
    obj_pat, methsends
  in
  make_conv_of_nested_tuple ~loc ~ids ~make_expr ~make_pat tyre_expr

let make_conv_tuple ~loc n tyre_expr =
  let gen = mk_gen "v" in
  let ids = List.init n (fun _ -> gen ()) in
  let make_expr ~loc l = A.Exp.tuple ~loc l in
  let make_pat ~loc () =
    let plids = List.map (AC.pvar ~loc) ids in
    let elids = List.map (AC.evar ~loc) ids in
    let ptuple = A.Pat.tuple ~loc plids in
    ptuple, elids
  in
  make_conv_of_nested_tuple ~loc ~ids ~make_expr ~make_pat tyre_expr

(** Converters to/from nested either types *)

let ppoly s ~loc x = A.Pat.(variant ~loc s (Some x))
let epoly s ~loc x = A.Exp.(variant ~loc s (Some x))
let make_nested_either_constr ~loc ~length ~mk n x =
  let rec nested_rights ~loc n expr =
    if n = 0 then expr
    else mk "Right" ~loc (nested_rights ~loc (n-1) expr)
  in
  if n = length - 1 then nested_rights ~loc n x
  else nested_rights ~loc n (mk "Left" ~loc x)

let make_match_from_nested ~loc mk_exprs =
  let length = List.length mk_exprs in
  let make_case n mk_expr =
    let id = "v" in
    A.Exp.case
      (make_nested_either_constr ~loc ~length ~mk:ppoly n @@ AC.pvar ~loc id)
      (mk_expr @@ AC.evar ~loc id)
  in
  A.Exp.function_ ~loc @@ List.mapi make_case mk_exprs

let make_match_to_nested ~loc mk_pats =
  let length = List.length mk_pats in
  let make_case n mk_pat =
    let id = "v" in
    A.Exp.case
      (mk_pat @@ AC.pvar ~loc id)
      (make_nested_either_constr ~loc ~length ~mk:epoly n @@ AC.evar ~loc id)
  in
  A.Exp.function_ ~loc @@ List.mapi make_case mk_pats

let make_conv_sum ~loc captures tyre_expr =
  let name_from_capture i = function
    | No ->
      Loc.raise_errorf ~loc
        "All alternatives branches must have a capturing group."
    | Unnamed _ -> Location.mkloc ("Alt"^string_of_int i) loc
    | Named s -> s
  in
  let branchnames = List.mapi name_from_capture captures in
  let fun_to =
    let expr_branchs =
      List.map (fun {Loc.loc;txt} -> epoly ~loc txt) branchnames
    in
    make_match_from_nested ~loc expr_branchs
  in
  let fun_from =
    let pat_branchs =
      List.map (fun {Loc.loc;txt} -> ppoly ~loc txt) branchnames
    in
    make_match_to_nested ~loc pat_branchs
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
  | Unnamed 1 | Unnamed 2 | Named [_] ->
    seq_expr
  | Unnamed i -> make_conv_tuple ~loc i seq_expr
  | Named l -> make_conv_object ~loc l seq_expr

(** Put everything together *)

let rec expr_of_regex (t : _ Regexp.t) =
  let loc = t.Loc.loc in
  match t.Loc.txt with
  | Regexp.Code r ->
    Tyre.mkf ~loc "regex" [Nolabel, r]
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
  | Repeat ({loc; _}, _) ->
    Loc.raise_errorf ~loc "Repetitions other than + and * are not implemented."
  | Nongreedy t ->
    Tyre.mkf ~loc "non_greedy" [Nolabel, expr_of_regex t]
  | Capture t -> expr_of_regex t
  | Capture_as (_, t) -> expr_of_regex t
  | Call lid -> A.Exp.ident lid


let adjust_position ~loc delim =
  let (+~) pos i = Lexing.{pos with pos_cnum = pos.pos_cnum + i } in
  match delim with
  | None -> loc.Loc.loc_start +~ 1
  | Some s -> loc.Loc.loc_start +~ (String.length s + 2)
let expr_of_string ~loc s delim =
  let pos = adjust_position ~loc delim in
  expr_of_regex @@ simplify @@ Regexp.parse_exn ~pos s


let rec regexp_of_pattern pat =
  let open Parsetree in
  let loc = pat.ppat_loc in
  let re = match pat.ppat_desc with
    | Ppat_constant (Pconst_string (s, delim)) ->
      let pos = adjust_position ~loc delim in
      (Regexp.parse_exn ~pos s).txt
    | Ppat_alias (pat, s) ->
      Regexp.(Capture_as (s, regexp_of_pattern pat))
    | Ppat_or (pat1, pat2) ->
      Regexp.(Alt [ regexp_of_pattern pat1 ; regexp_of_pattern pat2 ])
    | Ppat_any ->
      Regexp.Code ".*"
    | Ppat_var id ->
      Regexp.(Capture_as (id, {loc; txt = Code ".*"}))
    | _ ->
      Loc.raise_errorf ~loc
        "This pattern is not a valid tyre pattern."
  in
  Loc.mkloc re loc

let expr_of_pattern pat =
  let re = simplify @@ regexp_of_pattern pat in
  match re.txt with
  | Seq l ->
    let f_item re = capture re, expr_of_regex re in
    let capture_seq, expr = seq_to_expr ~loc:re.loc @@ List.map f_item l in
    capture_seq, expr
  | _ ->
    capture_singleton (capture re), expr_of_regex re


let expr_of_function ~loc l =
  let err_on_guard = function
    | None -> ()
    | Some e ->
      Loc.raise_errorf ~loc:e.Parsetree.pexp_loc
        "Tyre patterns can not have guards."
  in
  let route_of_case {Parsetree. pc_rhs ; pc_guard ; pc_lhs } =
    err_on_guard pc_guard;
    let loc = pc_lhs.ppat_loc in
    let capture, re = expr_of_pattern pc_lhs in
    let pvar_of_lid {Loc.loc; txt} = AC.pvar ~loc txt in
    let arg = match capture with
      | Named [] | Unnamed 0 -> internal_error ~loc
      | No | Unnamed _ -> A.Pat.any ~loc ()
      | Named [lid] -> pvar_of_lid lid
      | Named l -> AC.ptuple ~loc @@ List.map pvar_of_lid l 
    in
    let e = AC.func ~loc [arg, pc_rhs] in
    AC.constr ~loc "Tyre.Route" [re; e]
  in
  let l = List.map route_of_case l in
  Tyre.mkf ~loc "route" [Nolabel, AC.list ~loc l]

open Ast_mapper

let expr mapper e_ext =
  let open Parsetree in
  match e_ext.pexp_desc with
  | Pexp_extension ({txt = "tyre"; _},
                    PStr [{pstr_desc = Pstr_eval (e, _); _}]) ->
    let loc = e.pexp_loc in
    (match e.pexp_desc with
     | Pexp_constant (Pconst_string (s, delim)) ->
       expr_of_string ~loc s delim
     | Pexp_function l ->
       expr_of_function ~loc l
     | _ ->
       Loc.raise_errorf ~loc
        "[%%tyre] is only allowed on constant strings and functions.")
  | _ -> default_mapper.expr mapper e_ext

let () =
  Driver.register
    ~name:"ppx_regexp.tyre" ocaml_version
    (fun _config _cookies -> {default_mapper with expr})
