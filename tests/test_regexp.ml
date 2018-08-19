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

open Printf
module Loc = Location
module Q = QCheck

let mkloc = Loc.mkloc
let mknoloc = Loc.mknoloc
let map_loc f {Loc.txt = x; loc} = {Loc.txt = f x; loc}

module Regexp = struct
  include Regexp

  let nonepsilon = function {Location.txt = Seq []; _} -> false | _ -> true

  let rec collect_code = function
   | {Loc.txt = Code s1; loc = loc1} :: {Loc.txt = Code s2; loc = loc2} :: es ->
      let e12 =
        Loc.{
          txt = Code (s1 ^ s2);
          loc = {
            loc_start = loc1.loc_start;
            loc_end = loc2.loc_end;
            loc_ghost = loc1.loc_ghost || loc2.loc_ghost;
          }
        }
      in
      collect_code (e12 :: es)
   | es -> es

  let rec simplify e = map_loc simplify' e
  and simplify' = function
   | Code "" -> Seq []
   | Seq es ->
      let es = es
        |> List.map simplify
        |> List.map (function {Loc.txt = Seq es; _} -> es | e -> [e])
        |> List.flatten
        |> List.filter nonepsilon
      in
      (match es with
       | [e] -> e.Loc.txt
       | es -> Seq es)
   | Alt es ->
      let es = es
        |> List.map simplify
        |> List.map (function {Loc.txt = Alt es; _} -> es | e -> [e])
        |> List.flatten
      in
      (match es with
       | [e] -> e.Loc.txt
       | es -> Alt es)
   | Opt e ->
      (match simplify e with
       | {Loc.txt = Opt _; _} as e' -> e'.Loc.txt
       | e' -> Opt e')
   | Repeat (ij, e) -> Repeat (ij, simplify e)
   | Nongreedy e -> Nongreedy (simplify e)
   | Capture e -> Capture (simplify e)
   | Capture_as (name, e) -> Capture_as (name, simplify e)
   | Code _ | Call _ as e -> e

  let rec equal' e1 e2 =
    (match e1.Loc.txt, e2.Loc.txt with
     | Code s1, Code s2 -> s1 = s2
     | Seq es1, Seq es2 | Alt es1, Alt es2 ->
        (try List.for_all2 equal' es1 es2 with Invalid_argument _ -> false)
     | Opt e1, Opt e2 -> equal' e1 e2
     | Repeat ({Loc.txt = ij1; _}, e1), Repeat ({Loc.txt = ij2; _}, e2) ->
        ij1 = ij2 && equal' e1 e2
     | Nongreedy e1, Nongreedy e2 -> equal' e1 e2
     | Capture e1, Capture e2 -> equal' e1 e2
     | Capture_as (name1, e1), Capture_as (name2, e2) ->
        name1.Loc.txt = name2.Loc.txt && equal' e1 e2
     | Call name1, Call name2 -> name1.Loc.txt = name2.Loc.txt
     | _, _ -> false (* We'll notice. *))
  let equal e1 e2 = equal' (simplify e1) (simplify e2)

  let to_string =
    let p_bottom, p_alt, p_seq, p_suffix = 0, 1, 2, 3 in
    let delimit_if b s = if b then "(" ^ s ^ ")" else s in
    let rec aux p e =
      (match e.Loc.txt with
       | Code s ->
          delimit_if (p > p_seq) s
       | Seq es ->
          delimit_if (p > p_seq) (String.concat "" (List.map (aux p_seq) es))
       | Alt es ->
          delimit_if (p > p_alt) (String.concat "|" (List.map (aux p_alt) es))
       | Opt e ->
          delimit_if (p >= p_suffix) (aux p_suffix e ^ "?")
       | Repeat ({Loc.txt = (i, j_opt); _}, e) ->
          let j_str = match j_opt with None -> "" | Some j -> string_of_int j in
          delimit_if (p >= p_suffix)
            (sprintf "%s{%d,%s}" (aux p_suffix e) i j_str)
       | Nongreedy e ->
          aux (p_suffix - 1) e ^ "?"
       | Capture e ->
          "(+" ^ aux p_bottom e ^ ")"
       | Capture_as ({Loc.txt = name; _}, e) ->
          "(?<" ^ name ^ ">" ^ aux p_bottom e ^ ")"
       | Call {Loc.txt = idr; _} ->
          "(&" ^ String.concat "." (Longident.flatten idr) ^ ")")
    in
    aux 0

  let rec pp_debug ppf self =
    let open Regexp in
    let open Format in
    let open Location in

    let pp_pos ppf pos =
      let open Lexing in
      Format.fprintf ppf "%d:%d" pos.pos_lnum (pos.pos_cnum - pos.pos_bol)
    in
    let pp_loc ppf loc =
      let open Location in
      let open Lexing in
      if loc <> none then begin
        if loc.loc_start.pos_lnum = loc.loc_end.pos_lnum then
          Format.fprintf ppf "@%a-%d" pp_pos loc.loc_start
            (loc.loc_end.pos_cnum - loc.loc_end.pos_bol)
        else
          Format.fprintf ppf "@%a-%a" pp_pos loc.loc_start pp_pos loc.loc_end
      end
    in
    (match self.txt with
     | Code s ->
        fprintf ppf "(Code %S)" s
     | Seq es ->
        fprintf ppf "(Seq ";
        List.iter (pp_debug ppf) es;
        fprintf ppf ")";
     | Alt es ->
        fprintf ppf "(Alt ";
        List.iter (pp_debug ppf) es;
        fprintf ppf ")";
     | Opt e ->
        fprintf ppf "(Opt %a)" pp_debug e
     | Repeat ({txt = (i, j); loc}, e) ->
        let pp_option f ppf = function None -> () | Some e -> f ppf e in
        fprintf ppf "(Repeat {%d,%a}%a %a)"
          i (pp_option Format.pp_print_int) j pp_loc loc pp_debug e
     | Nongreedy e ->
        fprintf ppf "(Nongreedy %a)" pp_debug e
     | Capture e ->
        fprintf ppf "(Capture %a)" pp_debug e
     | Capture_as (name, e) ->
        fprintf ppf "(Capture_as %s%a %a)" name.txt pp_loc name.loc pp_debug e
     | Call name ->
        fprintf ppf "(Call %s%a)"
          (String.concat "." (Longident.flatten name.txt)) pp_loc name.loc);
    pp_loc ppf self.loc

  let show_debug e =
    let buf = Buffer.create 64 in
    let ppf = Format.formatter_of_buffer buf in
    pp_debug ppf e;
    Format.fprintf ppf " => %S" (to_string e);
    Format.pp_print_flush ppf ();
    Buffer.contents buf

  let rec to_re e =
    (match e.Loc.txt with
     | Code re -> Re.Perl.re re
     | Seq es -> Re.seq (List.map to_re es)
     | Alt es -> Re.alt (List.map to_re es)
     | Opt e -> Re.opt (to_re e)
     | Repeat ({Loc.txt = (i, j); _}, e) -> Re.repn (to_re e) i j
     | Nongreedy e -> Re.non_greedy (to_re e)
     | Capture e -> Re.group (to_re e)
     | Capture_as (_, e) -> Re.group (to_re e)
     | Call _ -> raise Re.Perl.Not_supported)

  let rec has_anon_capture e =
    (match e.Loc.txt with
     | Code _ | Call _ -> false
     | Seq es | Alt es -> List.exists has_anon_capture es
     | Opt e | Repeat (_, e) | Capture_as (_, e) | Nongreedy e ->
        has_anon_capture e
     | Capture _ -> true)

end

let gen_name =
  let open Q.Gen in
  let idrletter i =
    if i = 0 then '_' else let i = i - 1 in
    if i < 26 then Char.chr (0x61 + i) else let i = i - 26 in
    if i < 26 then Char.chr (0x41 + i) else let i = i - 26 in
    (assert (i < 10); Char.chr (0x30 + i))
  in
  let idrfst = map idrletter (int_bound (27 - 1)) in
  let idrcnt = map idrletter (int_bound (63 - 1)) in
  map2 (fun c s -> String.make 1 c ^ s) idrfst (string ~gen:idrcnt)

let gen_regexp =
  let open Q.Gen in
  let open Regexp in
  let gen_char = map (fun c -> mknoloc (Code (String.make 1 c))) numeral in
  let gen_backlash_op =
    let backslash_ops = "wWsSdDbBAZzG" in
    map (fun i -> mknoloc (Code (sprintf "\\%c" backslash_ops.[i])))
        (int_bound (String.length backslash_ops - 1)) in
  let gen_quoted_op =
    let quotable = "!\"#$%&'()*+,-./:=<=>?@[\\]^`{|}~" in
    map (fun i -> mknoloc (Code (sprintf "\\%c" quotable.[i])))
        (int_bound (String.length quotable - 1)) in
  map Regexp.simplify @@ sized @@
  fix @@ fun self n ->
    let gen_seq =
      map (fun es -> mknoloc (Seq es))
        ((0 -- 10) >>= fun k -> list_size (return k) (self (n / (max 1 k)))) in
    let gen_alt =
      map (fun es -> mknoloc (Alt es))
        ((2 -- 10) >>= fun k -> list_size (return k) (self (n / (max 1 k)))) in
    let gen_opt =
      map (fun e -> mknoloc (Opt e)) (self n) in
    let gen_repeat =
      map2 (fun i e -> mknoloc (Repeat (mknoloc (i, None), e))) nat (self n) in
    let gen_capture =
      map (fun e -> mknoloc (Capture e)) (self n) in
    let gen_capture_as =
      map2 (fun a e -> mknoloc (Capture_as (mknoloc a, e))) gen_name (self n) in
    frequency [
      1, gen_char;
      1, gen_backlash_op;
      1, gen_quoted_op;
      n*(n - 1), gen_seq;
      n*(n - 1), gen_alt;
      n, gen_opt;
      n, gen_repeat;
      n, gen_capture;
      n, gen_capture_as;
    ]

let shrink_regexp =
  let open Q.Shrink in
  let open Q.Iter in
  let open Regexp in
  let rec shrink e =
    (match e.Loc.txt with
     | Code s -> map (fun s -> mknoloc (Code s)) (string s)
     | Seq es -> map (fun es -> mknoloc (Seq es)) (list ~shrink es)
     | Alt (e :: es) ->
        map2 (fun e es -> mknoloc (Alt (e :: es))) (shrink e) (list ~shrink es)
     | Opt e -> map (fun e -> mknoloc (Opt e)) (shrink e)
     | Repeat ({Loc.txt = (i, j); _}, e) ->
        map2 (fun (i, j) e -> mknoloc (Repeat (mknoloc (i, j), e)))
          (pair (int i) (option int j)) (shrink e)
     | Capture e -> map (fun e -> mknoloc (Capture e)) (shrink e)
     | Capture_as (name, e) ->
        map2 (fun name e -> mknoloc (Capture_as (mknoloc name, e)))
          (string name.Loc.txt) (shrink e)
     | _ -> empty)
  in
  fun e -> map Regexp.simplify (shrink e)

let arb_regexp =
  Q.make ~print:Regexp.show_debug ~shrink:shrink_regexp gen_regexp

let test_parse s =
  let r =
    (match Regexp.parse_exn s with
     | exception Location.Error err -> Error err
     | e ->
        Ok (e,
          (try Ok (Regexp.to_re e) with
           | Re.Perl.Parse_error -> Error `Parse_error
           | Re.Perl.Not_supported -> Error `Not_supported)))
  in
  let r' =
    try Ok (Re.Perl.re s) with
     | Re.Perl.Parse_error -> Error `Parse_error
     | Re.Perl.Not_supported -> Error `Not_supported
  in
  (match r, r' with
   | (Error _ | Ok (_, Error _)),       Error _ -> true
   | Ok _,                              Error `Not_supported -> true
   | Ok (e, Ok _),                      Error `Parse_error ->
      if Regexp.has_anon_capture e then true else
      Q.Test.fail_reportf "Parsed to %a and converted to Re.t, \
                           but should be invalid" Regexp.pp_debug e
   | Error err,                         Ok _ ->
      Q.Test.fail_reportf "Failed to parse valid %s: %a" s
          Location.report_error err
   | Ok (e, Error _),                   Ok _ ->
      Q.Test.fail_reportf "Parsed to %a but conversion to Re.t failed"
        Regexp.pp_debug e
   | Ok (_, Ok _),                      Ok _ ->
      (* TODO: Would have been nice to compare the two Re.t here. *)
      true)

let tests = [
  Q.Test.make ~long_factor:100 ~name:"parse ∘ to_string" arb_regexp
    (fun e ->
      (match Regexp.parse_exn (Regexp.to_string e) with
       | exception Location.Error err ->
          Q.Test.fail_reportf "%a" Location.report_error err
       | e' -> Regexp.equal e' e));
  Q.Test.make ~long_factor:100 ~name:"to_string ∘ parse"
    (Q.string_gen Q.Gen.printable) test_parse;
]

let () = QCheck_runner.run_tests_main tests
