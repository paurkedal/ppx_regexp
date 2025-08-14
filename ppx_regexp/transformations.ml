open Ppxlib
open Ast_builder.Default

module Regexp = struct
  open Regexp_types
  include Regexp

  let bindings =
    let rec recurse must_match (e' : _ Location.loc) =
      let loc = e'.Location.loc in
      match e'.Location.txt with
      | Code _ -> fun acc -> acc
      | Seq es -> Util.List.fold (recurse must_match) es
      | Alt es -> Util.List.fold (recurse false) es
      | Opt e -> recurse false e
      | Repeat ({ Location.txt = i, _; _ }, e) -> recurse (must_match && i > 0) e
      | Nongreedy e -> recurse must_match e
      | Capture _ -> Util.error ~loc "Unnamed capture is not allowed for %%pcre and %%mikmatch."
      | Capture_as (idr, conv, e) -> fun (nG, bs) -> recurse must_match e (nG + 1, (idr, Some nG, conv, must_match) :: bs)
      | Named_subs (idr, None, conv, e) | Named_subs (_, Some idr, conv, e) ->
        fun (nG, bs) -> recurse must_match e (nG + 1, (idr, Some nG, conv, must_match) :: bs)
      | Unnamed_subs (_, e) -> recurse must_match e
      | Pipe_all (res, func, e) ->
        fun (nG, bs) ->
          let nG', inner_bs = recurse must_match e (nG, []) in
          nG', ((res, None, Some (Pipe_all_func func), must_match) :: inner_bs) @ bs
      | Call _ -> Util.error ~loc "(&...) is not implemented for %%pcre and %%mikmatch."
    in
    function { Location.txt = Capture_as (idr, conv, e); _ } -> recurse true e (0, [ idr, None, conv, true ]) | e -> recurse true e (0, [])

  let to_re_expr ~ctx =
    let rec recurse ~ctx (e' : _ Location.loc) =
      let loc = e'.Location.loc in
      match e'.Location.txt with
      | Code s -> [%expr Re.Perl.re [%e estring ~loc s]]
      | Seq es ->
        let exprs = List.map (recurse ~ctx) es in
        [%expr Re.seq [%e elist ~loc exprs]]
      | Alt es ->
        let exprs = List.map (recurse ~ctx) es in
        [%expr Re.alt [%e elist ~loc exprs]]
      | Opt e -> [%expr Re.opt [%e recurse ~ctx e]]
      | Repeat ({ Location.txt = i, j_opt; _ }, e) ->
        let e_i = eint ~loc i in
        let e_j = match j_opt with None -> [%expr None] | Some j -> [%expr Some [%e eint ~loc j]] in
        [%expr Re.repn [%e recurse ~ctx e] [%e e_i] [%e e_j]]
      | Nongreedy e -> [%expr Re.non_greedy [%e recurse ~ctx e]]
      | Capture _ -> Util.error ~loc "Unnamed capture is not allowed for %%pcre and %%mikmatch."
      | Capture_as (_, _, e) -> [%expr Re.group [%e recurse ~ctx e]]
      | Named_subs (idr, _, _, _) ->
        let content = get_substitution ~loc ~ctx idr in
        [%expr Re.group [%e recurse ~ctx content]]
      | Unnamed_subs (idr, _) ->
        let content = get_substitution ~loc ~ctx idr in
        recurse ~ctx content
      | Pipe_all (_, _, e) -> recurse ~ctx e
      | Call _ -> Util.error ~loc "Call is not allowed for %%pcre and %%mikmatch."
    and get_substitution ~loc ~ctx idr =
      let var_name = idr.txt in
      match Util.Ctx.find var_name ctx with
      | Some value -> value
      | None -> Util.error ~loc "Variable '%s' not found. %%pcre and %%mikmatch only support global let bindings for substitution." var_name
    in
    function { Location.txt = Capture_as (_, _, e); _ } -> recurse ~ctx e | e -> recurse ~ctx e

  let to_string ~ctx =
    let p_alt, p_seq, p_suffix, p_atom = 0, 1, 2, 3 in
    let delimit_if b s = if b then "(?:" ^ s ^ ")" else s in
    let get_parsed ~loc idr =
      let var_name = idr.txt in
      let content =
        match Util.Ctx.find var_name ctx with
        | Some value -> value
        | None ->
          Util.error ~loc "Variable '%s' not found. %%pcre and %%mikmatch only support global let bindings for substitution." var_name
      in
      content
    in
    let rec recurse p (e' : _ Location.loc) =
      let loc = e'.Location.loc in
      match e'.Location.txt with
      | Code s ->
        (* Delimiters not needed as Regexp.parse_exn only returns single
         * chars, csets, and escape sequences. *)
        s
      | Seq es -> delimit_if (p > p_seq) (String.concat "" (List.map (recurse p_seq) es))
      | Alt es -> delimit_if (p > p_alt) (String.concat "|" (List.map (recurse p_alt) es))
      | Opt e ->
        let content = recurse p_atom e in
        let result = if p >= p_seq then "(?:" ^ content ^ ")?" else content ^ "?" in
        delimit_if (p > p_suffix) result
      | Repeat ({ Location.txt = i, j_opt; _ }, e) ->
        let j_str = match j_opt with None -> "" | Some j -> string_of_int j in
        delimit_if (p > p_suffix) (Printf.sprintf "%s{%d,%s}" (recurse p_atom e) i j_str)
      | Nongreedy e -> recurse p_suffix e ^ "?"
      | Capture _ -> Util.error ~loc "Unnamed capture is not allowed for %%pcre and %%mikmatch."
      | Capture_as (_, _, e) -> "(" ^ recurse p_alt e ^ ")"
      | Named_subs (idr, _, _, _) ->
        let content = get_parsed ~loc idr in
        "(" ^ recurse p_alt content ^ ")"
      | Unnamed_subs (idr, _) ->
        let content = get_parsed ~loc idr in
        recurse p_atom content
      | Pipe_all (_, _, e) -> recurse p_alt e
      | Call _ -> Util.error ~loc "(&...) is not implemented for %%pcre and %%mikmatch."
    in
    function { Location.txt = Capture_as (_, _, e); _ } -> recurse 0 e | e -> recurse 0 e
end

let rec wrap_group_bindings ~loc ~captured_acc rhs offG = function
  | [] -> rhs
  | [ (varG, _, Some (Regexp_types.Pipe_all_func func_name), _) ] ->
    let func_ident = pexp_ident ~loc { txt = Util.extract_qualified_name func_name; loc } in
    let captured = List.rev captured_acc in
    let func_app = List.fold_left (fun expr arg -> [%expr [%e expr] [%e arg]]) func_ident captured in
    [%expr
      let [%p ppat_var ~loc varG] = [%e func_app] in
      [%e rhs]]
  | (varG, iG, conv, mustG) :: bs ->
    let eG = match iG with None -> [%expr Re.Group.get _g 0] | Some iG -> [%expr Re.Group.get _g [%e eint ~loc (offG + iG + 1)]] in
    let eG =
      match conv with
      | None -> eG
      | Some Regexp_types.Int -> [%expr int_of_string [%e eG]]
      | Some Regexp_types.Float -> [%expr float_of_string [%e eG]]
      | Some (Regexp_types.Func func_name) ->
        let func_ident = pexp_ident ~loc { txt = Util.extract_qualified_name func_name; loc } in
        [%expr [%e func_ident] [%e eG]]
      | Some (Regexp_types.Pipe_all_func _) ->
        Util.error ~loc "No >>> allowed inside patterns" (* parser makes sure this is never the case *)
    in
    let eG = if mustG then eG else [%expr try Some [%e eG] with Not_found -> None] in

    let pat = ppat_var ~loc varG in
    let pat_ident = pexp_ident ~loc @@ { txt = Util.extract_qualified_name varG.txt; loc = varG.loc } in
    [%expr
      let [%p pat] = [%e eG] in
      [%e wrap_group_bindings ~loc ~captured_acc:(pat_ident :: captured_acc) rhs offG bs]]

let rec separate_defaults acc = function
  | [] -> List.rev acc, []
  | ({ pc_lhs = { ppat_desc = Ppat_any; _ }; _ } as case) :: rest -> acc, case :: rest
  | ({ pc_lhs = { ppat_desc = Ppat_var _; _ }; _ } as case) :: rest -> acc, case :: rest
  | case :: rest -> separate_defaults (case :: acc) rest

let rec create_opts ~loc = function
  | [] -> [%expr []]
  | `Caseless :: xs -> [%expr `Caseless :: [%e create_opts ~loc xs]]
  | `Anchored :: xs -> [%expr `Anchored :: [%e create_opts ~loc xs]]

let extract_bindings ~(parser : ?pos:position -> string -> string Regexp_types.t) ~ctx ~pos s =
  let r = parser ~pos s in
  let nG, bs = Regexp.bindings r in
  (* let re_str = Regexp.to_string ~ctx r in *)
  let re = Regexp.to_re_expr ~ctx r in
  (* let loc = Location.none in *)
  re, bs, nG

let make_default_rhs ~loc = function
  | [] ->
    let open Lexing in
    let pos = loc.Location.loc_start in
    let e0 = estring ~loc pos.pos_fname in
    let e1 = eint ~loc pos.pos_lnum in
    let e2 = eint ~loc (pos.pos_cnum - pos.pos_bol) in
    let e = [%expr raise (Match_failure ([%e e0], [%e e1], [%e e2]))] in
    Util.warn ~loc "A universal case is recommended." e
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
    (match transformed with
    | [ { pc_lhs = { ppat_desc = Ppat_any; _ }; pc_guard = None; pc_rhs; _ } ] -> pc_rhs
    | _ -> pexp_match ~loc [%expr _ppx_regexp_v] transformed)

let transform_let ~mode ~ctx =
  let parser = match mode with `Pcre -> Regexp.parse_exn ~target:`Let | `Mik -> Regexp.parse_mik_exn ~target:`Let in
  List.map
    begin
      fun vb ->
        match vb.pvb_pat.ppat_desc, vb.pvb_expr.pexp_desc with
        | Ppat_var { txt = var_name; loc }, Pexp_constant (Pconst_string (value, _, _)) ->
          if Util.check_unbounded_recursion ~mode var_name value then Util.error ~loc "Unbounded recursion detected!"
          else begin
            let string_loc = vb.pvb_expr.pexp_loc in
            let pos = string_loc.loc_start in
            let pos = { pos with pos_cnum = pos.pos_cnum + 2 (* skip opening *) } in
            let parsed = parser ~pos value in
            Hashtbl.replace ctx var_name parsed;
            let warning_attr =
              attribute ~loc ~name:{ txt = "ocaml.warning"; loc }
                ~payload:(PStr [ { pstr_desc = Pstr_eval (estring ~loc "-32", []); pstr_loc = loc } ])
            in
            { vb with pvb_attributes = warning_attr :: vb.pvb_attributes }
          end
        | _ -> vb
    end

let transform_cases ~mode ~opts ~loc ~ctx cases =
  let _ = opts in
  let aux case =
    Ast_pattern.(parse (pstring __'))
      loc case.pc_lhs
      begin
        fun { txt = re_src; loc = { loc_start; loc_end; _ } } ->
          let re_offset = (loc_end.pos_cnum - loc_start.pos_cnum - String.length re_src) / 2 in
          let pos = { loc_start with pos_cnum = loc_start.pos_cnum + re_offset; pos_lnum = loc_end.pos_lnum } in
          let parser = match mode with `Pcre -> Regexp.parse_exn ~target:`Match | `Mik -> Regexp.parse_mik_exn ~target:`Match in
          let re, bs, nG = extract_bindings ~parser ~pos ~ctx re_src in
          re, nG, bs, case.pc_rhs, case.pc_guard
      end
  in

  let group_by_guard_and_re cases =
    let rec group acc current_group = function
      | [] -> if current_group = [] then acc else current_group :: acc
      | ((re, _, _, _, guard) as case) :: rest ->
        (match current_group with
        | [] -> group acc [ case ] rest
        | cases_in_group ->
          let can_merge =
            match guard with
            | None -> List.for_all (fun (_, _, _, _, g) -> g = None) cases_in_group
            | Some _ -> List.exists (fun (re', _, _, _, _) -> re = re') cases_in_group
          in
          if can_merge then group acc (case :: current_group) rest else group (List.rev current_group :: acc) [ case ] rest)
    in
    group [] [] cases
  in

  let compile_group group_idx group_cases =
    let pattern_groups =
      List.fold_left
        (fun acc (re, nG, bs, rhs, guard) ->
          let found, updated =
            List.fold_left
              (fun (found, acc_groups) (re', cases) ->
                if found then found, (re', cases) :: acc_groups
                else if re = re' then true, (re', (nG, bs, rhs, guard) :: cases) :: acc_groups
                else false, (re', cases) :: acc_groups)
              (false, []) acc
          in
          if found then updated else (re, [ nG, bs, rhs, guard ]) :: updated)
        [] group_cases
      |> List.rev
    in

    let patterns_with_offsets =
      let result, _ =
        List.fold_left
          (fun (acc, offG) (re, case_handlers) ->
            let nG =
              let n, _, _, _ = List.hd (List.rev case_handlers) in
              n
            in
            (re, case_handlers, offG) :: acc, offG + nG)
          ([], 0) pattern_groups
      in
      List.rev result
    in

    let re_array = pexp_array ~loc @@ List.map (fun (re, _, _) -> re) patterns_with_offsets in

    let handlers =
      List.mapi
        (fun i (_, case_handlers, offG) ->
          let handler_name = Printf.sprintf "_group%d_case_%d" group_idx i in
          let handler_body =
            let rec mk_guard_chains = function
              | [] -> [%expr None]
              | (_, bs, rhs, guard) :: rest ->
                let bs = List.rev bs in
                (match guard with
                | None -> [%expr Some [%e wrap_group_bindings ~captured_acc:[] ~loc rhs offG bs]]
                | Some guard_expr ->
                  let guarded = [%expr if [%e guard_expr] then Some [%e rhs] else [%e mk_guard_chains rest]] in
                  wrap_group_bindings ~captured_acc:[] ~loc guarded offG bs)
            in
            [%expr fun _g -> [%e mk_guard_chains (List.rev case_handlers)]]
          in
          handler_name, handler_body)
        patterns_with_offsets
    in

    re_array, handlers
  in
  let apply_opts re_expr =
    let rec apply re = function
      | [] -> re
      | `Caseless :: rest -> apply [%expr Re.no_case [%e re]] rest
      | `Anchored :: rest -> apply [%expr Re.whole_string [%e re]] rest
    in
    apply re_expr opts
  in

  let cases, default_cases = separate_defaults [] cases in
  let default_rhs = make_default_rhs ~loc default_cases in
  let processed_cases = List.map aux cases in
  let case_groups = group_by_guard_and_re processed_cases in

  let compiled_groups =
    List.mapi
      (fun i group_cases ->
        let re_var_name = Util.fresh_var () in
        let re_array, handlers = compile_group i group_cases in
        re_var_name, re_array, handlers)
      case_groups
  in

  let re_bindings =
    List.map
      (fun (var_name, re_array, _) ->
        let is_single = match re_array.pexp_desc with Pexp_array [ _ ] -> true | _ -> false in

        let comp_expr =
          if is_single then (
            (* Single pattern - no marks needed *)
            let single_re = match re_array.pexp_desc with Pexp_array [ re ] -> re | _ -> assert false in
            [%expr
              let re = Re.compile [%e apply_opts single_re] in
              re, [||]])
          else (
            (* Multiple patterns - apply opts to each then mark *)
            let res_with_opts =
              match re_array.pexp_desc with
              | Pexp_array res -> res |> List.map (fun re -> [%expr Re.mark [%e apply_opts re]])
              | _ -> assert false
            in
            [%expr
              let a = [%e pexp_array ~loc res_with_opts] in
              let marks = Array.map fst a in
              let re = Re.compile (Re.alt (Array.to_list (Array.map snd a))) in
              re, marks])
        in
        value_binding ~loc ~pat:(ppat_var ~loc { txt = var_name; loc }) ~expr:comp_expr)
      compiled_groups
  in

  let handler_bindings =
    List.concat_map
      (fun (_, _, handlers) ->
        List.map (fun (name, body) -> value_binding ~loc ~pat:(ppat_var ~loc { txt = name; loc }) ~expr:body) handlers)
      compiled_groups
  in

  let match_expr =
    let groups_with_info =
      List.mapi
        (fun i (re_var_name, re_array, handlers) ->
          let group_cases = List.nth case_groups i in
          let has_guards = List.exists (fun (_, _, _, _, g) -> g <> None) group_cases in

          (* Check if this is truly a single pattern by looking at the re_array *)
          let is_single_pattern =
            match re_array.pexp_desc with
            | Pexp_array [ _ ] -> true (* Only one RE in the array *)
            | Pexp_array [] -> true (* Empty array (shouldn't happen) *)
            | _ -> false
          in

          i, re_var_name, handlers, has_guards, is_single_pattern)
        compiled_groups
    in

    let match_cascade =
      [%expr
        let rec __ppx_regexp_try_next group_idx =
          [%e
            let group_cases =
              List.map
                (fun (idx, re_var_name, handlers, has_guards, is_single_pattern) ->
                  let match_expr =
                    if is_single_pattern then (
                      (* Single pattern - call handler directly, no dispatcher *)
                      let handler_name = fst (List.hd handlers) in
                      [%expr
                        match Re.exec_opt (fst [%e pexp_ident ~loc { txt = Lident re_var_name; loc }]) _ppx_regexp_v with
                        | None -> __ppx_regexp_try_next ([%e eint ~loc idx] + 1)
                        | Some _g ->
                          (* Direct call to handler, no dispatcher *)
                          (match [%e pexp_ident ~loc { txt = Lident handler_name; loc }] _g with
                          | Some result -> result
                          | None ->
                            (* Handler returned None - guard must have failed *)
                            __ppx_regexp_try_next ([%e eint ~loc idx] + 1))])
                    else (
                      (* Multiple patterns: need marks and dispatcher *)
                      let handlers_array =
                        pexp_array ~loc @@ List.map (fun (name, _) -> pexp_ident ~loc { txt = Lident name; loc }) handlers
                      in

                      if has_guards then
                        [%expr
                          match Re.exec_opt (fst [%e pexp_ident ~loc { txt = Lident re_var_name; loc }]) _ppx_regexp_v with
                          | None -> __ppx_regexp_try_next ([%e eint ~loc idx] + 1)
                          | Some _g ->
                            (match
                               __ppx_regexp_dispatch (snd [%e pexp_ident ~loc { txt = Lident re_var_name; loc }]) [%e handlers_array] _g
                             with
                            | Some result -> result
                            | None -> __ppx_regexp_try_next ([%e eint ~loc idx] + 1))]
                      else
                        [%expr
                          match Re.exec_opt (fst [%e pexp_ident ~loc { txt = Lident re_var_name; loc }]) _ppx_regexp_v with
                          | None -> __ppx_regexp_try_next ([%e eint ~loc idx] + 1)
                          | Some _g ->
                            (match
                               __ppx_regexp_dispatch (snd [%e pexp_ident ~loc { txt = Lident re_var_name; loc }]) [%e handlers_array] _g
                             with
                            | Some result -> result
                            | None -> assert false)])
                  in

                  case ~lhs:(ppat_constant ~loc (Pconst_integer (string_of_int idx, None))) ~guard:None ~rhs:match_expr)
                groups_with_info
            in

            let default_case = case ~lhs:(ppat_any ~loc) ~guard:None ~rhs:default_rhs in

            pexp_match ~loc [%expr group_idx] (group_cases @ [ default_case ])]
        in
        __ppx_regexp_try_next 0]
    in
    match_cascade
  in

  let match_expr = if handler_bindings = [] then match_expr else pexp_let ~loc Nonrecursive handler_bindings match_expr in

  match_expr, re_bindings

(* processes each case individually instead of combining them into one RE *)
let transform_mixed_match ~loc ~ctx ?matched_expr cases acc =
  let aux case =
    match case.pc_lhs.ppat_desc with
    | Ppat_extension
        ( { txt = ("pcre" | "mikmatch" | "pcre_i" | "mikmatch_i") as ext; _ },
          (* anchored *)
          PStr [ { pstr_desc = Pstr_eval ({ pexp_desc = Pexp_constant (Pconst_string (pat, str_loc, _)); _ }, _); _ } ] ) ->
      let pos = str_loc.loc_start in
      let mode, opts = if String.starts_with ~prefix:"pcre" ext then `Pcre, [] else `Mik, Util.mikmatch_default_opts in
      let opts = if String.ends_with ~suffix:"_i" ext then `Caseless :: opts else opts in
      let parser = match mode with `Pcre -> Regexp.parse_exn ~target:`Match | `Mik -> Regexp.parse_mik_exn ~target:`Match in
      let re, bs, nG = extract_bindings ~parser ~pos ~ctx pat in
      `Ext (opts, re, nG, bs, case.pc_rhs, case.pc_guard)
    | _ -> `Regular case
  in

  let prepared_cases = List.map aux cases in

  let has_ext = List.exists (function `Ext _ -> true | _ -> false) prepared_cases in

  if not has_ext then begin
    match matched_expr with None -> pexp_function ~loc cases, acc | Some m -> pexp_match ~loc m cases, acc
  end
  else begin
    let compilations =
      List.mapi
        begin
          fun i case ->
            match case with
            | `Ext (opts, re, _, _, _, _) ->
              let comp_var = Util.fresh_var () in
              let apply_opts re_expr =
                let rec apply re = function
                  | [] -> re
                  | `Caseless :: rest -> apply [%expr Re.no_case [%e re]] rest
                  | `Anchored :: rest -> apply [%expr Re.whole_string [%e re]] rest
                in
                apply re_expr opts
              in
              let re_with_opts = apply_opts re in
              let comp_expr = [%expr Re.compile [%e re_with_opts]] in
              let binding = value_binding ~loc ~pat:(ppat_var ~loc { txt = comp_var; loc }) ~expr:comp_expr in
              Some (i, comp_var, binding)
            | _ -> None
        end
        prepared_cases
      |> List.filter_map (fun x -> x)
    in

    let bindings = List.map (fun (_, _, b) -> b) compilations in

    let rec build_ordered_match input_var case_idx cases comps =
      match cases, comps with
      | [], _ ->
        (* should not happen if original had catch-all *)
        [%expr raise (Match_failure ("", 0, 0))]
      | `Regular case :: rest, _ ->
        [%expr
          match [%e input_var] with
          | [%p case.pc_lhs] when [%e Option.value case.pc_guard ~default:[%expr true]] -> [%e case.pc_rhs]
          | _ -> [%e build_ordered_match input_var (case_idx + 1) rest comps]]
      | `Ext (_, _, _, bs, rhs, guard) :: rest, (idx, comp_var, _) :: rest_comps when idx = case_idx ->
        let comp_ident = pexp_ident ~loc { txt = Lident comp_var; loc } in
        [%expr
          match Re.exec_opt [%e comp_ident] [%e input_var] with
          | Some _g ->
            [%e
              let bs = List.rev bs in
              match guard with
              | None -> wrap_group_bindings ~captured_acc:[] ~loc rhs 0 bs
              | Some g ->
                let guarded_rhs = [%expr if [%e g] then [%e rhs] else [%e build_ordered_match input_var (case_idx + 1) rest rest_comps]] in
                wrap_group_bindings ~captured_acc:[] ~loc guarded_rhs 0 bs]
          | None -> [%e build_ordered_match input_var (case_idx + 1) rest rest_comps]]
      | `Ext _ :: rest, _ ->
        (* shouldn't happen if indices are correct *)
        build_ordered_match input_var (case_idx + 1) rest comps
    in

    let match_body = build_ordered_match [%expr _ppx_regexp_v] 0 prepared_cases compilations in

    let match_expr =
      match matched_expr with
      | None -> [%expr fun _ppx_regexp_v -> [%e match_body]]
      | Some m ->
        [%expr
          let _ppx_regexp_v = [%e m] in
          [%e match_body]]
    in
    match_expr, bindings @ acc
  end
