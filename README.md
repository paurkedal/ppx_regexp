`ppx_regexp` - Matching Regular Expressions with OCaml Patterns
---------------------------------------------------------------

This syntax extension turns
```ocaml
match%pcre x with
| {|re1|} -> e1
...
| {|reN|} -> eN
| _ -> e0
```
into suitable invocations of the
[Re library](https://github.com/ocaml/ocaml-re).  The patterns are plain
strings of the form accepted by `Re_pcre`, except groups can be bound to
variables using the syntax `(?<var>...)`.  The type of `var` will be
`string` if a match is of the groups is guaranteed given a match of the
whole pattern, and `string option` if the variable is bound to or nested
below an optionally matched group.

## Example

The following prints out times and hosts for SMTP connections to the Postfix
daemon:
```ocaml
(* Link with re, re.pcre, lwt, lwt.unix.
   Preprocess with ppx_regexp.
   Adjust to your OS. *)

open Lwt.Infix

let check_line =
  (function%pcre
   | {|(?<t>.*:\d\d) .* postfix/smtpd\[[0-9]+\]: connect from (?<host>[a-z0-9.-]+)|} ->
      Lwt_io.printlf "%s %s" t host
   | _ ->
      Lwt.return_unit)

let () = Lwt_main.run begin
  Lwt_io.printl "SMTP connections from:" >>= fun () ->
  Lwt_stream.iter_s check_line (Lwt_io.lines_of_file "/var/log/syslog")
end
```

## Limitations

- The processor is currently new and not well tested.  Please break it and
  file bug reports.
- Pattern guards are not implemented.
- Optional patterns due to `?`, `*`, and `{0,n}` are detected.  If you find
  other reasons a `Re_pcre` pattern may opt, please file a bug report.
- Is it feasible to cover any reasonable ground with exhaustiveness checks?
  No attempt is currently made, and no warning is issued for a missing
  match-all case.
