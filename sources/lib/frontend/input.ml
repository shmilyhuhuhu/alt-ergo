(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2018-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

exception Parse_only

module type S = sig

  (* Parsing *)

  type expr

  type file

  val parse_expr : Lexing.lexbuf -> expr

  val parse_file : filename:string -> preludes:string list -> file

  (* Typechecking *)

  type env

  val new_id : unit -> int

  val type_expr :
    env -> (Symbols.t * Ty.t) list -> expr -> int Typed.atterm

  val type_file : file -> (int Typed.atdecl * env) list * env
end

let input_methods = ref []

let register name ((module M : S) as m) =
  input_methods := (name, m) :: !input_methods

let find name = List.assoc name !input_methods

