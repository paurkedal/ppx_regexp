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

let () =
  (match%pcre "%" with _ -> ());
  (match%pcre "%" with s -> assert (s = "%"));
  (function%pcre _ -> ()) "%";
  (function%pcre s -> assert (s = "%")) "%"

let test1 =
  (function%pcre
   | {|^(?<k>.*): *(?<v>.+)?$|} -> `Attr (k, v)
   | {|^# (?<comment>.+)$|} -> `Comment comment
   | {|^((?<last>[@%]){2}){0,2}$|} -> `Even_sigils last
   | {|^[@%]|} -> `Odd_sigils
   | _ -> `Unknown)

let () =
  assert (test1 "x: 1" = `Attr ("x", Some "1"));
  assert (test1 "# Kommentar" = `Comment "Kommentar");
  assert (test1 "" = `Even_sigils None);
  assert (test1 "%%%@" = `Even_sigils (Some "@"));
  assert (test1 "%%@" = `Odd_sigils)

let last_elt s =
  let n = String.length s in
  assert (s.[n - 1] = ';');
  let i = try String.rindex_from s (n - 2) ';' + 1 with Not_found -> 0 in
  String.sub s i (n - i - 1)

let rec test2 s =
  (match%pcre s with
   | {|^<>$|} -> assert (s = "<>")
   | {|^<(?<x>[^<>]+)>$|} -> assert (s = "<" ^ x ^ ">")
   | {|^<(?<x>[^<>]+)><(?<y>[^<>]+)>$|} -> assert (s = "<" ^ x ^ "><" ^ y ^ ">")
   | {|^((?<elt>[^;<>]);)+$|} -> assert (elt = last_elt s)
   | {|^[^{}]*\{(?<s'>.*)\}|} -> test2 s'
   | _ -> assert false)

let test3 s =
  (match%pcre s with
   | {|no(is)((e)) (?<is>is) (g(oo)d)|} -> assert (is = "is")
   | {|?<s'>&()[a-zA-Z0-9_-]+(;)|} ->
      let i, j = String.index s '&', String.rindex s ';' in
      assert (s' = String.sub s i (j - i + 1))
   | {|m(o+)re re(gular)? no(is)e, (no )*be(t+)?er|} -> ()
   | s' -> assert (s = s'))

let () =
  test2 "<>";
  test2 "<a>";
  test2 "<ab>";
  test2 "<a><b>";
  test2 "<ab><cde>";
  test2 "a;";
  test2 "a;b;c;d;";
  test2 "<a;b>";
  test2 "Xx{--{a;b;c;}--}yY.";
  test3 "- + &nbsp; + -";
  test3 "catch-all"

(* It should work in a functor, and Re_pcre.regxp should be lifted to the
 * top-level. *)
module F (M : Map.OrderedType) = struct
  let f x =
    (match%pcre x with
     | {|#(?<space>\s)?(?<comment>.*)|} -> Some (space <> None, comment)
     | _ -> None)
end

(* It should work as a top-level eval. *)
let r = ref false
;;(match%pcre "" with
   | {|^$|} -> r := true
   | _ -> assert false)
;;assert (!r = true)
