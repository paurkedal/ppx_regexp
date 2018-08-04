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

let test re s =
  match Tyre.exec re s with
  | Ok b -> b
  | Error e ->
    Format.eprintf "Error: %a@." Tyre.pp_error e;
    assert false
let (%%) = test
let (%%%) a b = assert (a %% b)

let () =
  (function%tyre _ -> true) %%% "%";
  (function%tyre s -> s = "%") %%%"%"

type t = [
  | `Attr of string * string option
  | `Comment of string
  | `Even_sigils of string option
  | `Odd_sigils
  | `Unknown ]

let test1 : t Tyre.re =
  (function%tyre
   | {|^(?<k>.*): *(?<v>.+)?$|} -> `Attr (k, v)
   | {|^# (?<comment>.+)$|} -> `Comment comment
   | {|^(?<sigil>([@%]{2})+)?$|} -> `Even_sigils sigil
   | {|^[@%]|} -> `Odd_sigils
   | _ -> `Unknown)

let () =
  assert (test1 %% "x: 1" = `Attr ("x", Some "1"));
  assert (test1 %% "# Kommentar" = `Comment "Kommentar");
  assert (test1 %% "" = `Even_sigils None);
  assert (test1 %% "%%%@" = `Even_sigils (Some "%%%@"));
  assert (test1 %% "%%@" = `Odd_sigils)

let concat_gen sep gen =
  let rec f () =
    match gen () with
    | None -> ""
    | Some s -> s ^ sep ^ f ()
  in
  f ()

let test2 = function%tyre
  | {|^<>$|} -> (=) "<>"
  | {|^<(?<x>[^<>]+)>$|} -> fun s -> s = "<" ^ x ^ ">"
  | {|^<(?<x>[^<>]+)><(?<y>[^<>]+)>$|} -> fun s -> s = "<" ^ x ^ "><" ^ y ^ ">"
  | {|^((?<elt>[^;<>]);)*$|} -> fun s -> concat_gen ";" elt = s
  | {|^(?<a>one)|(?<b>two)$|} as x ->
    (match x with
     | `a a -> fun s -> a = s && a = "one"
     | `b b -> fun s -> b = s && b = "two")

let (%%%%) re s = (re %% s) s

let () =
  assert (test2 %%%%"<>");
  assert (test2 %%%%"<a>");
  assert (test2 %%%%"<ab>");
  assert (test2 %%%%"<a><b>");
  assert (test2 %%%%"<ab><cde>");
  assert (test2 %%%%"a;");
  assert (test2 %%%%"a;b;c;d;");
  assert (test2 %%%%"<a;b>");
  assert (test2 %%%%"one");
  assert (test2 %%%%"two")

(* It should work in a functor, and Re_pcre.regxp should be lifted to the
 * top-level. *)
module F (M : Map.OrderedType) = struct
  let f = function%tyre
    | {|#(?<space>\s)?(?<comment>.*)|} -> Some (space <> None, comment)
    | _ -> None
end
