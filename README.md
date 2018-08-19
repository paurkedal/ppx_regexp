[![Build Status][ci-build-status]][ci]

# Two PPXes for Working with Regular Expressions

This repo provides two PPXes providing regular expression-based routing:

- `ppx_regexp` maps to [re][] with the conventional last-match extraction
  into `string` and `string option`.  It works directly on strings.
- `ppx_tyre` maps to [Tyre][tyre] providing typed extraction into options,
  lists, tuples, objects, and polymorphic variants.  It defines `Tyre.t` and
  `Tyre.route` values.

Another difference is that `ppx_regexp` works directly on strings
essentially hiding the library calls, while `ppx_tyre` provides `Tyre.t` and
`Tyre.route` which can be composed an applied using the Tyre library.

## `ppx_regexp` - Regular Expression Matching with OCaml Patterns

This syntax extension turns
```ocaml
function%pcre
| {|re1|} -> e1
...
| {|reN|} -> eN
| _ -> e0
```
into suitable invocations of the [Re library][re], and similar for
`match%pcre`.  The patterns are plain strings of the form accepted by
`Re_pcre`, with the following additions:

  - `(?<var>...)` defines a group and binds whatever it matches as `var`.
    The type of `var` will be `string` if the match is guaranteed given that
    the whole pattern matches, and `string option` if the variable is bound
    to or nested below an optionally matched group.

  - `?<var>` at the start of a pattern binds group 0 as `var : string`.
    This may not be the full string if the pattern is unanchored.

A variable is allowed for the universal case and is bound to the matched
string.  A regular alias is currently not allowed for patterns, since it is
not obvious whether is should bind the full string or group 0.

### Example

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

## `ppx_tyre` - Syntax Support for Tyre Routes

This PPX compiles
```ocaml
    [%tyre {|re|}]
```
into `'a Tyre.t` and
```ocaml
    function%tyre
    | {|re1|} as x1 -> e1
    ...
    | {|reN|} as x2 -> eN
```
into `'a Type.route`, where `re`, `re1`, ... are regular expressions
expressed in a slightly extended subset of PCRE.  The interpretations are:

- `re?` extracts an option of what `re` extracts.
- `re+`, `re*`, `re{n,m}` extracts a list of what `re` extracts.
- `(?@qname)` refers to any identifier bound to a typed regular expression
  of type `'a Tyre.t`.
- One or more `(?<v>re)` at the top level can be used to bind variables
  instead of `as ...`.
- One or more `(?<v>re)` in a sequence extracts an object where each method
  `v` is bound to what `re` extracts.
- An alternative with one `(?<v>re)` per branch extracts a polymorphic
  variant where each constructor `` `v`` receives what `re` extracts as its
  argument.
- `(?&v:qname)` is a shortcut for `(?<v>(?&qname))`.

## Limitations

### No Pattern Guards

Pattern guards are not supported.  This is due to the fact that all match
cases are combined into a single regular expression, so if one of the
patterns succeed, the match is committed before we can check the guard
condition.

### No Exhaustiveness Check

The syntax extension will always warn if no catch-all case is provided.  No
exhaustiveness check is attempted.  Doing it right would require
reimplementing full regular expression parsing and an algorithm which would
ideally produce a counter-example.

## Bug Reports

The processor is currently new and not well tested.  Please break it and
file bug reports in the GitHub issue tracker.  Any exception raised by
generated code except for `Match_failure` is a bug.


[ci]: https://travis-ci.org/paurkedal/ppx_compose
[ci-build-status]: https://travis-ci.org/paurkedal/ppx_regexp.svg?branch=master
[re]: https://github.com/ocaml/ocaml-re
[tyre]: https://github.com/Drup/tyre
