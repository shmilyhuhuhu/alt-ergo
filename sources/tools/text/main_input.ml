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

let () =
  let module M : Input.S = struct

    type expr = unit

    type file = unit

    let parse_expr _ = ()

    let parse_file ~filename ~preludes = ()

    type env = unit

    let new_id () = 0

    let type_expr _ _ _ = assert false

    let type_file _ = [], ()

  end in
  Input.register "dolmen" (module M)

