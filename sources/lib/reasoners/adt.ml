(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

open Options
open Format
open Sig

module Sy = Symbols
module E  = Expr
module Hs = Hstring

type 'a abstract =
  | Constr of { c_name : Hs.t ; c_ty : Ty.t ; c_args : (Hs.t * 'a) list }
  | Select of { d_name : Hs.t ; d_ty : Ty.t ; d_arg : 'a }
  | Tester of { t_name : Hs.t ; t_arg : 'a }
  | Alien of 'a

module type ALIEN = sig
  include Sig.X
  val embed : r abstract -> r
  val extract : r -> (r abstract) option
end


let constr_of_destr ty dest =
  if debug_adt () then fprintf fmt "ty = %a@." Ty.print ty;
  match ty with
  | Ty.Tadt (s, params, cases) ->
    begin
      try
        List.find
          (fun (c, destrs) ->
             List.exists (fun (d, _) -> Hstring.equal dest d) destrs
          )cases
      with Not_found -> assert false (* invariant *)
    end
  | _ -> assert false


module Shostak (X : ALIEN) = struct

  type t = X.r abstract
  type r = X.r

  module SX = Set.Make(struct type t = r let compare = X.hash_cmp end)

  let name = "Adt"

  [@@ocaml.ppwarning "XXX: IsConstr not interpreted currently"]
  [@@ocaml.ppwarning "XXX: remove useless case Destructor from Symbols"]
  let is_mine_symb sy ty =
    match sy, ty with
    | Sy.Op (Sy.Constr _), Ty.Tadt _ -> true
    | Sy.Op Sy.Destruct (_, guarded), _ -> true
    | _ -> false

  let embed r =
    match X.extract r with
    | Some c -> c
    | None -> Alien r

  let print fmt = function
    | Alien x ->
      fprintf fmt "%a" X.print x

    | Constr {c_name; c_args} ->
      fprintf fmt "%a" Hs.print c_name;
      begin
        match c_args with
          [] -> ()
        | (lbl, v) :: l ->
          fprintf fmt "(%a : %a " Hs.print lbl X.print v;
          List.iter
            (fun (lbl, v) ->
               fprintf fmt "; %a : %a" Hs.print lbl X.print v) l;
          fprintf fmt ")"
      end

    | Select d ->
      fprintf fmt "%a#!%a" X.print d.d_arg Hs.print d.d_name
    | Tester t ->
      fprintf fmt "(%a ? %a)" X.print t.t_arg Hs.print t.t_name


  [@@ocaml.ppwarning "TODO: canonization is missing"]
  let is_mine u =
    match u with
    | Alien r -> r
    | Constr _ | Tester _ -> X.embed u
    | Select {d_arg; d_name} ->
      match embed d_arg with
      | Constr c ->
        begin
          try snd @@ List.find (fun (lbl, v) -> Hs.equal d_name lbl) c.c_args
          with Not_found ->
            fprintf fmt "is_mine %a failed@." print u;
            assert false
        end
      | _ -> X.embed u

  let equal s1 s2 =
    match s1, s2 with
    | Alien r1, Alien r2 -> X.equal r1 r2
    | Constr c1, Constr c2 ->
      Hstring.equal c1.c_name c2.c_name &&
      Ty.equal c1.c_ty c2.c_ty &&
      begin
        try
          List.iter2
            (fun (hs1, v1) (hs2, v2) ->
               assert (Hs.equal hs1 hs2);
               if not (X.equal v1 v2) then raise Exit
            )c1.c_args c2.c_args;
          true
        with
        | Exit -> false
        | _ -> assert false
      end

    | Select d1, Select d2 ->
      Hstring.equal d1.d_name d2.d_name &&
      Ty.equal d1.d_ty d2.d_ty &&
      X.equal d1.d_arg d2.d_arg

    | Tester t1, Tester t2 ->
      Hstring.equal t1.t_name t2.t_name &&
      X.equal t1.t_arg t2.t_arg

    | _ -> false


  [@@ocaml.ppwarning "TODO: canonization is missing"]
  let make t =
    if debug_adt () then
      eprintf "make %a@." E.print t;
    let {E.f; xs; ty} = match E.term_view t with
      | E.Term t -> t
      | E.Not_a_term _ -> assert false
    in
    let _sx, ctx =
      List.fold_left
        (fun (args, ctx) s ->
           let rs, ctx' = X.make s in
           rs :: args, List.rev_append ctx' ctx
        )([], []) xs
    in
    let xs = List.rev _sx in
    match f, xs, ty with
    | Sy.Op Sy.Constr hs, _, Ty.Tadt (_,_,cases) ->
      let case_hs = try List.assoc hs cases with Not_found -> assert false in
      let c_args =
        try
          List.rev @@
          List.fold_left2
            (fun c_args v (lbl, _) -> (lbl, v) :: c_args)
            [] xs case_hs
        with _ -> assert false
      in
      is_mine @@
      Constr {c_name = hs; c_ty = ty; c_args}, ctx

    | Sy.Op Sy.Destruct (hs, guarded), [e], _ ->
      let sel = Select {d_name = hs ; d_arg = e ; d_ty = ty} in
      if not guarded then is_mine sel, ctx
      else
        X.term_embed t, ctx
    (* No risk !
         if equal sel (embed sel_x) then X.term_embed t, ctx
         else sel_x, ctx (* canonization OK *)
    *)
    | _ ->
      assert false

  let hash = function
    | Alien r ->
      X.hash r

    | Constr { c_name ; c_ty ; c_args } ->
      List.fold_left
        (fun acc (_, r) -> acc * 7 + X.hash r)
        (Hstring.hash c_name + 7 * Ty.hash c_ty) c_args

    | Select { d_name ; d_ty ; d_arg } ->
      ((Hstring.hash d_name + 11 * Ty.hash d_ty)) * 11 + X.hash d_arg

    | Tester { t_name ; t_arg } ->
      Hstring.hash t_name * 13 + X.hash t_arg

  let leaves r =
    let l = match r with
      | Alien r -> [Hs.empty, r]
      | Constr { c_args ; _ } ->  c_args
      | Select { d_arg  ; _ } -> [Hs.empty, d_arg]
      | Tester { t_arg  ; _ } -> [Hs.empty, t_arg]
    in
    SX.elements @@
    List.fold_left
      (fun sx (_, r) ->
         List.fold_left (fun sx x -> SX.add x sx) sx (X.leaves r)
      )SX.empty l

  [@@ocaml.ppwarning "TODO: not sure"]
  let fully_interpreted sb = false (* not sure *)

  let type_info = function
    | Alien r -> X.type_info r
    | Constr { c_ty ; _ } ->  c_ty
    | Select { d_ty  ; _ } -> d_ty
    | Tester _ -> Ty.Tbool

  exception Out of int

  let compare s1 s2 =
    match embed s1, embed s2 with
    | Alien r1, Alien r2 -> X.str_cmp r1 r2
    | Alien r1, _ -> 1
    | _, Alien r2 -> -1

    | Constr c1, Constr c2 ->
      let c = Hstring.compare c1.c_name c2.c_name in
      if c <> 0 then c
      else
        let c = Ty.compare c1.c_ty c2.c_ty in
        if c <> 0 then c
        else
          begin
            try
              List.iter2
                (fun (hs1, v1) (hs2, v2) ->
                   assert (Hs.equal hs1 hs2);
                   let c = X.str_cmp v1 v2 in
                   if c <> 0 then raise (Out c);
                )c1.c_args c2.c_args;
              0
            with
            | Out c -> c
            | _ -> assert false
          end
    | Constr _, _ -> 1
    | _, Constr _ -> -1

    | Select d1, Select d2 ->
      let c = Hstring.compare d1.d_name d2.d_name in
      if c <> 0 then c
      else
        let c = Ty.compare d1.d_ty d2.d_ty in
        if c <> 0 then c
        else X.str_cmp d1.d_arg d2.d_arg

    | Select _, _ -> 1
    | _, Select _ -> -1

    | Tester t1, Tester t2 ->
      let c = Hstring.compare t1.t_name t2.t_name in
      if c <> 0 then c
      else
        X.str_cmp t1.t_arg t2.t_arg

  let abstract_selectors p acc =
    match p with
    | Alien r -> assert false (* handled in Combine *)
    | Constr { c_args } ->
      let acc, args =
        List.fold_left (fun (acc, l) (lbl, x) ->
            let y, acc = X.abstract_selectors x acc in
            if not (X.equal x y)
                [@ocaml.ppwarning "TODO: abstract Selectors"] then
              assert false; (* TODO *)
            acc, (lbl, y) :: l
          ) (acc, []) c_args
      in
      is_mine p, acc

    | Tester {t_arg} ->
      let s_arg, acc = X.abstract_selectors t_arg acc in
      if not (X.equal s_arg t_arg)
          [@ocaml.ppwarning "TODO: abstract Selectors"] then
        assert false;
      is_mine p, acc

    | Select ({d_arg} as s)  [@ocaml.ppwarning "TODO: abstract Selectors"] ->
      (* no need to abstract THIS selector. It's necessiraly
         toplevel in ADTs *)
      let s_arg, acc = X.abstract_selectors d_arg acc in
      if not (X.equal s_arg d_arg)
          [@ocaml.ppwarning "TODO: abstract Selectors"] then
        assert false;
      let x = is_mine @@ Select {s with d_arg=s_arg} in
      begin match embed x  with
        | Select ({d_name; d_ty; d_arg} as s) ->
          let cstr, cstr_args = constr_of_destr (X.type_info d_arg) d_name in
          let xs = List.map (fun (_, ty) -> E.fresh_name ty) cstr_args in
          let cons =
            E.mk_term (Sy.constr (Hs.view cstr)) xs (X.type_info d_arg)
          in
          if debug_adt () then
            fprintf fmt "abstr with equality %a == %a@."
              X.print d_arg E.print cons;
          let cons, _ = make cons in
          let acc = (d_arg, cons) :: acc in
          let xx = is_mine @@ Select {s with d_arg = cons} in
          if debug_adt () then
            fprintf fmt "%a becomes %a@." X.print x  X.print xx;
          xx, acc

        | _ ->
          x, acc

      end


  let is_alien_of e x =
    List.exists (fun y -> X.equal x y) (X.leaves e)

  let solve r1 r2 pb =
    if debug_adt () then
      Format.eprintf "[ADTs] solve %a = %a@." X.print r1 X.print r2;
    match embed r1, embed r2 with
    | Select _, _ | _, Select _ -> assert false (* should be eliminated *)
    | Tester _, _ | _, Tester _ -> assert false (* not interpreted *)
    | Alien _, Alien _ ->
      { pb with
        sbt = (if X.str_cmp r1 r2 > 0 then r1, r2 else r2, r1) :: pb.sbt }

    | Alien r, Constr _ ->
      if is_alien_of r2 r then raise Util.Unsolvable;
      { pb with sbt = (r, r2) :: pb.sbt }

    | Constr _, Alien r ->
      if is_alien_of r1 r then raise Util.Unsolvable;
      { pb with sbt = (r, r1) :: pb.sbt }

    | Constr c1, Constr c2 ->
      if not (Hstring.equal c1.c_name c2.c_name) then raise Util.Unsolvable;
      try
        {pb with
         eqs =
           List.fold_left2
             (fun eqs (hs1, v1) (hs2, v2) ->
                assert (Hstring.equal hs1 hs2);
                (v1, v2) :: eqs
             )pb.eqs c1.c_args c2.c_args
        }
      with Invalid_argument _ -> assert false


  [@@ocaml.ppwarning "TODO: canonization is missing"]

  let subst p v s =
    match s with
    | Alien r -> if X.equal p r then v else X.subst p v r
    | Constr c ->
      is_mine @@
      Constr
        { c with
          c_args = List.map (fun (lbl, u) -> lbl, X.subst p v u) c.c_args }

    | Select d ->
      is_mine @@ Select { d with d_arg = X.subst p v d.d_arg }

    | Tester t ->
      is_mine @@ Tester { t with t_arg = X.subst p v t.t_arg }


  let color _        = assert false

  let term_extract _ = None, false


  let assign_value r _ eq = assert false
  let choose_adequate_model t _ l = assert false


  (***

     (*BISECT-IGNORE-BEGIN*)
     module Debug = struct

     let solve_bis a b =
      if debug_sum () then fprintf fmt "[Sum] we solve %a = %a@."
        X.print a X.print b

     let solve_bis_result res =
      if debug_sum () then
        match res with
          | [p,v] -> fprintf fmt "\twe get: %a |-> %a@." X.print p X.print v
          | []    -> fprintf fmt "\tthe equation is trivial@."
          | _ -> assert false

     let solve_bis_unsolvable () =
      if debug_sum () then fprintf fmt "\tthe equation is unsolvable@."

     end
     (*BISECT-IGNORE-END*)

     let print = Debug.print

   ***)
end
