let () =
  let module M : Input.S = struct

    (* Parsing *)

    type expr = Parsed.lexpr

    type file = Parsed.file

    let parse_expr l = Parsers.parse_expr l

    let parse_file = Parsers.parse_problem

    (** Typechecking *)

    include Typechecker

  end in
  Input.register "legacy" (module M)

