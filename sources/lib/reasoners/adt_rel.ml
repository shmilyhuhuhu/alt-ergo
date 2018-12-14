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

module X = Shostak.Combine
module Sh = Shostak.Adt
open Sh

type r = X.r
type uf = Uf.t

module Ex = Explanation
module E = Expr
module SE = E.Set
module Hs = Hstring
module HSS = Hs.Set
module Sy = Symbols

module MX = Map.Make (struct type t = X.r let compare = X.hash_cmp end)
module LR = Uf.LX
module MHs = Hs.Map

type t =
  {
    classes : E.Set.t list;
    domains : (HSS.t * Explanation.t) MX.t;
    seen_destr : SE.t;
    seen_access : SE.t;
    seen_testers : HSS.t MX.t;
    [@ocaml.ppwarning "selectors should be improved. only representatives \
                       in it. No true or false _is"]

      selectors : (E.t * Ex.t) list MHs.t MX.t;
    size_splits : Numbers.Q.t;
    new_terms : SE.t;
    pending_deductions : (E.t * Ex.t) list;
  }

let empty classes = {
  classes;
  domains = MX.empty;
  seen_destr = SE.empty;
  seen_access = SE.empty;
  seen_testers = MX.empty;
  selectors = MX.empty;
  size_splits = Numbers.Q.one;
  new_terms = SE.empty;
  pending_deductions = [];
}


(* ################################################################ *)
(*BISECT-IGNORE-BEGIN*)
module Debug = struct

  let assume bol r1 r2 =
    if debug_adt () then
      fprintf fmt "[Sum.Rel] we assume %a %s %a@."
        X.print r1 (if bol then "=" else "<>") X.print r2

  let print_env loc env =
    if debug_adt () then begin
      fprintf fmt "--ADT env %s ---------------------------------@." loc;
      MX.iter
        (fun r (hss, ex) ->
           fprintf fmt "%a ::= " X.print r;
           begin
             match HSS.elements hss with
               []      -> ()
             | hs :: l ->
               fprintf fmt " %s" (Hs.view hs);
               List.iter (fun hs -> fprintf fmt " | %s" (Hs.view hs)) l
           end;
           fprintf fmt " : %a@." Ex.print ex;

        ) env.domains;
      fprintf fmt "-- seen testers ---------------------------@.";
      MX.iter
        (fun r hss ->
           HSS.iter
             (fun hs ->
                fprintf fmt "(%a is %a)@." X.print r Hs.print hs
             )hss
        )env.seen_testers;
      fprintf fmt "-- selectors ------------------------------@.";
      MX.iter
        (fun r mhs ->
           MHs.iter
             (fun hs l ->
                List.iter (fun (a, _) ->
                    fprintf fmt "(%a is %a) ==> %a@."
                      X.print r Hs.print hs E.print a
                  ) l
             )mhs
        )env.selectors;
      fprintf fmt "-------------------------------------------@.";
    end

  let case_split r r' =
    if debug_adt () then
      fprintf fmt "[ADT.case-split] %a = %a@." X.print r X.print r'

  let no_case_split () =
    if debug_adt () then fprintf fmt "[ADT.case-split] nothing@."

  let add r =
    if debug_adt () then fprintf fmt "ADT.Rel.add: %a@." X.print r

end
(*BISECT-IGNORE-END*)
(* ################################################################ *)


let print_model fmt env l = ()
let new_terms env = env.new_terms
let instantiate ~do_syntactic_matching _ env uf _ = env, []

let assume_th_elt t th_elt dep =
  assert false


let values_of ty =
  match ty with
  | Ty.Tadt (_,_,l) ->
    Some (List.fold_left (fun st (hs, _) -> HSS.add hs st) HSS.empty l)
  | _ -> None

let add_adt env t r sy ty =
  if MX.mem r env.domains then env
  else
    match sy, ty with
    | Sy.Op Sy.Constr hs, Ty.Tadt _ ->
      if debug_adt () then Format.eprintf "new ADT expr(C): %a@." E.print t;
      { env with domains =
                   MX.add r (HSS.singleton hs, Ex.empty) env.domains }

    | _, Ty.Tadt _ ->
      if debug_adt () then Format.eprintf "new ADT expr: %a@." E.print t;
      let constrs =
        match values_of ty with None -> assert false | Some s -> s
      in
      { env with domains = MX.add r (constrs, Ex.empty) env.domains }

    | _ -> env

let seen_tester r hs env =
  try HSS.mem hs (MX.find r env.seen_testers)
  with Not_found -> false

let update_tester r hs env =
  let old = try MX.find r env.seen_testers with Not_found -> HSS.empty in
  {env with seen_testers = MX.add r (HSS.add hs old) env.seen_testers}

let trivial_tester r hs =
  match embed r with (* can filter further/better *)
  | Adt.Constr {c_name} -> Hstring.equal c_name hs
  | _ -> false

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


[@@ocaml.ppwarning "XXX improve. For each selector, store its \
                    corresponding constructor when typechecking ?"]
let add_guarded_destr env uf t hs e t_ty =
  if debug_adt () then
    Format.eprintf "new (guarded) Destr: %a@." E.print t;
  let env = { env with seen_destr = SE.add t env.seen_destr } in
  let c, _ = constr_of_destr (E.type_info e) hs in
  let access = E.mk_term (Sy.destruct (Hs.view hs) ~guarded:false) [e] t_ty in
  let is_c = E.mk_builtin true (Sy.IsConstr c) [e] in
  let eq = E.mk_eq access t ~iff:false in
  if debug_adt () then begin
    fprintf fmt "associated with constr %a@." Hstring.print c;
    fprintf fmt "%a => %a@." E.print is_c E.print eq;
  end;
  let r_e, ex_e = try Uf.find uf e with Not_found -> assert false in
  if trivial_tester r_e c then
    {env with pending_deductions = (eq, ex_e) :: env.pending_deductions}
  else
  if seen_tester r_e c env then
    {env with pending_deductions = (eq, ex_e) :: env.pending_deductions}
  else
    let m_e = try MX.find r_e env.selectors with Not_found -> MHs.empty in
    let old = try MHs.find c m_e with Not_found -> [] in
    { env with selectors =
                 MX.add r_e (MHs.add c ((eq, ex_e)::old) m_e)
                   env.selectors }


[@@ocaml.ppwarning "working with X.term_extract r would be sufficient ?"]
let add env (uf:uf) (r:r) t =
  let {E.f=sy; xs; ty} = match E.term_view t with
    | E.Term t -> t
    | E.Not_a_term _ -> assert false
  in
  let env = add_adt env t r sy ty in
  match sy, xs with
  | Sy.Op Sy.Destruct (hs, true), [e] -> (* guarded *)
    if debug_adt () then
      fprintf fmt "[ADTs] add guarded destruct: %a@." E.print t;
    if (SE.mem t env.seen_destr) then env
    else add_guarded_destr env uf t hs e ty

  | Sy.Op Sy.Destruct (_, false), [_] -> (* not guarded *)
    if debug_adt () then
      fprintf fmt "[ADTs] add unguarded destruct: %a@." E.print t;
    { env with seen_access = SE.add t env.seen_access }

  | Sy.Op Sy.Destruct _, _ ->
    assert false (* not possible *)

  (*| Sy.Op Sy.IsConstr _, _ ->
     if debug_adt () then
       Format.eprintf "new Tester: %a@." E.print t;
     { env with seen_testers = SE.add t env.seen_testers }
  *)
  | _ -> env

let add env uf r t =
  Debug.print_env "before add" env;
  let env = add env uf r t in
  Debug.print_env "after add" env;
  env

let count_splits env la =
  let nb =
    List.fold_left
      (fun nb (_,_,_,i) ->
         match i with
         | Th_util.CS (Th_util.Th_sum, n) -> Numbers.Q.mult nb n
         | _ -> nb
      )env.size_splits la
  in
  {env with size_splits = nb}

let deduce_is_constr uf r h eqs env ex =
  let r, ex' = try Uf.find_r uf r with Not_found -> assert false in
  let ex = Ex.union ex ex' in
  match embed r with
  | Adt.Alien r ->
    begin match X.term_extract r with
      | Some t, _ ->
        let eqs =
          if seen_tester r h env then eqs
          else
            let is_c = E.mk_builtin true (Sy.IsConstr h) [t] in
            if debug_adt () then
              fprintf fmt "[deduce is_constr] %a@." E.print is_c;
            (Sig_rel.LTerm is_c, ex, Th_util.Other) :: eqs
        in
        begin
          match E.term_view t with
          | E.Not_a_term _ -> assert false
          | E.Term {E.ty = Ty.Tadt (_,_,cases) as ty} ->
            (* Only do this deduction for finite types ??
                 may not terminate in some cases otherwise.
                 eg. type t = A of t
                 goal g: forall e,e' :t. e = C(e') -> false
                 + should not be guareded by "seen_tester"
            *)
            let c, args =
              try List.find (fun (c, _) -> Hstring.equal h c) cases
              with Not_found -> assert false
            in
            let xs = List.map (fun (_, ty) -> E.fresh_name ty) args in
            let cons = E.mk_term (Sy.constr (Hs.view h)) xs ty in
            let env = {env with new_terms = SE.add cons env.new_terms} in
            let eq = E.mk_eq t cons ~iff:false in
            if debug_adt () then
              fprintf fmt "[deduce equal to constr] %a@." E.print eq;
            let eqs = (Sig_rel.LTerm eq, ex, Th_util.Other) :: eqs in
            env, eqs
          | _ -> env, eqs
        end
      | _ ->
        fprintf fmt "%a@." X.print r;
        assert false
    end
  | _ -> env,eqs

let add_diseq uf hss sm1 sm2 dep env eqs =
  match sm1, sm2 with
  | Adt.Alien r , Adt.Constr {c_name = h; c_args = []}
  | Adt.Constr {c_name = h; c_args = []}, Adt.Alien r  ->
    (* not correct with args *)
    let enum, ex =
      try MX.find r env.domains with Not_found -> hss, Ex.empty
    in
    let enum = HSS.remove h enum in
    let ex = Ex.union ex dep in
    if HSS.is_empty enum then raise (Ex.Inconsistent (ex, env.classes))
    else
      let env = { env with domains = MX.add r (enum, ex) env.domains } in
      if HSS.cardinal enum = 1 then
        let h' = HSS.choose enum in
        let env, eqs = deduce_is_constr uf r h' eqs env ex in
        env, eqs
      else env, eqs

  | Adt.Alien r , Adt.Constr _ | Adt.Constr _, Adt.Alien r  ->
    env, eqs

  | Adt.Alien r1, Adt.Alien r2 ->
    let enum1,ex1=
      try MX.find r1 env.domains with Not_found -> hss,Ex.empty in
    let enum2,ex2=
      try MX.find r2 env.domains with Not_found -> hss,Ex.empty in

    let env, eqs =
      if HSS.cardinal enum1 = 1 then
        let ex = Ex.union dep ex1 in
        let h' = HSS.choose enum1 in
        deduce_is_constr uf r1 h' eqs env ex
      else env, eqs
    in
    let env, eqs =
      if HSS.cardinal enum2 = 1 then
        let ex = Ex.union dep ex2 in
        let h' = HSS.choose enum2 in
        deduce_is_constr uf r2 h' eqs env ex
      else env, eqs
    in
    env, eqs

  |  _ -> env, eqs

let assoc_and_remove_selector hs r env =
  try
    let mhs = MX.find r env.selectors in
    let deds = MHs.find hs mhs in
    let mhs = MHs.remove hs mhs in
    deds,
    (if MHs.is_empty mhs then {env with selectors = MX.remove r env.selectors}
     else {env with selectors = MX.add r mhs env.selectors})

  with Not_found ->
    [], env

let assume_is_constr uf hs r dep env eqs =
  match embed r with
  | Adt.Constr{c_name} when not (Hs.equal c_name hs) ->
    raise (Ex.Inconsistent (dep, env.classes));
  | _ ->
    if debug_adt () then
      fprintf fmt "assume is constr %a %a@." X.print r Hs.print hs;
    if seen_tester r hs env then
      env, eqs
    else
      let deds, env = assoc_and_remove_selector hs r env in
      let eqs =
        List.fold_left
          (fun eqs (ded, dep') ->
             (Sig_rel.LTerm ded, Ex.union dep dep', Th_util.Other) :: eqs
          )eqs deds
      in
      let env = update_tester r hs env in

      let enum, ex =
        try MX.find r env.domains
        with Not_found ->
        (*Cannot just put assert false !
          some terms are not well inited *)
        match values_of (X.type_info r) with
        | None -> assert false
        | Some s -> s, Ex.empty
      in
      let ex = Ex.union ex dep in
      if not (HSS.mem hs enum) then raise (Ex.Inconsistent (ex, env.classes));
      let env, eqs = deduce_is_constr uf r hs eqs env ex in
      {env with domains = MX.add r (HSS.singleton hs, ex) env.domains} , eqs

let assume_not_is_constr uf hs r dep env eqs =
  match embed r with
  | Adt.Constr{c_name} when Hs.equal c_name hs ->
    raise (Ex.Inconsistent (dep, env.classes));
  | _ ->

    let _, env = assoc_and_remove_selector hs r env in
    let enum, ex =
      try MX.find r env.domains with
        Not_found ->
        (* semantic values may be not inited with function add *)
        match values_of (X.type_info r) with
        | Some s -> s, Ex.empty
        | None -> assert false
    in
    if not (HSS.mem hs enum) then env, eqs
    else
      let enum = HSS.remove hs enum in
      let ex = Ex.union ex dep in
      if HSS.is_empty enum then raise (Ex.Inconsistent (ex, env.classes))
      else
        let env = { env with domains = MX.add r (enum, ex) env.domains } in
        if HSS.cardinal enum = 1 then
          let h' = HSS.choose enum in
          let env, eqs = deduce_is_constr uf r h' eqs env ex in
          env, eqs
        else env, eqs



(* dot it modulo equivalence class ? or is it sufficient ? *)
let add_eq uf hss sm1 sm2 dep env eqs =
  match sm1, sm2 with
  | Adt.Alien r, Adt.Constr {c_name=h} | Adt.Constr {c_name=h}, Adt.Alien r  ->
    let enum, ex =
      try MX.find r env.domains with Not_found -> hss, Ex.empty
    in
    let ex = Ex.union ex dep in
    if not (HSS.mem h enum) then raise (Ex.Inconsistent (ex, env.classes));
    let env, eqs = deduce_is_constr uf r h eqs env ex in
    {env with domains = MX.add r (HSS.singleton h, ex) env.domains} , eqs

  | Adt.Alien r1, Adt.Alien r2   ->
    let enum1,ex1 =
      try MX.find r1 env.domains with Not_found -> hss, Ex.empty in
    let enum2,ex2 =
      try MX.find r2 env.domains with Not_found -> hss, Ex.empty in
    let ex = Ex.union dep (Ex.union ex1 ex2) in
    let diff = HSS.inter enum1 enum2 in
    if HSS.is_empty diff then raise (Ex.Inconsistent (ex, env.classes));
    let domains = MX.add r1 (diff, ex) env.domains in
    let env = {env with domains = MX.add r2 (diff, ex) domains } in
    if HSS.cardinal diff = 1 then begin
      fprintf fmt "XXX: make a deduction here@.";
      let h' = HSS.choose diff in
      let env, eqs = deduce_is_constr uf r1 h' eqs env ex in
      let env, eqs = deduce_is_constr uf r2 h' eqs env ex in

           (*
           let ty = X.type_info r1 in
           env,
           (LSem (LR.mkv_eq r1 (is_mine (Cons(h',ty)))), ex, Sig.Other)::eqs
            *)
      env, eqs
    end
    else env, eqs

  |  _ -> env, eqs


let add_aux env r =
  Debug.add r;
  match embed r with
  | Adt.Alien r when not (MX.mem r env.domains) ->
    begin match values_of (X.type_info r) with
      | Some s -> { env with domains = MX.add r (s, Ex.empty) env.domains }
      | None ->
        env
    end
  | _ -> env

(* needed for models generation because fresh terms are not
   added with function add *)
let add_rec env r = List.fold_left add_aux env (X.leaves r)

let update_cs_modulo_eq r1 r2 ex env eqs =
  (* PB Here: even if Subst, we are not sure that it was
     r1 |-> r2, because LR.mkv_eq may swap r1 and r2 *)
  try
    let old = MX.find r1 env.selectors in
    if debug_adt () then
      fprintf fmt "update selectors modulo eq: %a |-> %a@."
        X.print r1 X.print r2;
    let mhs = try MX.find r2 env.selectors with Not_found -> MHs.empty in
    let eqs = ref eqs in
    let _new =
      MHs.fold
        (fun hs l mhs ->
           if trivial_tester r2 hs then begin
             if debug_adt () then
               fprintf fmt "make deduction because %a ? %a is trivial @."
                 X.print r2 Hs.print hs;
             List.iter
               (fun (a, dep) ->
                  eqs := (Sig_rel.LTerm a, dep, Th_util.Other) :: !eqs) l;
           end;
           let l = List.rev_map (fun (a, dep) -> a, Ex.union ex dep) l in
           MHs.add hs l mhs
        )old mhs
    in
    { env with selectors = MX.add r2 _new env.selectors }, !eqs
  with Not_found -> env, eqs

let assume env uf la =
  let env = count_splits env la in
  let classes = Uf.cl_extract uf in
  let env = { env with classes = classes } in
  let aux bol r1 r2 dep env eqs = function
    | None     -> env, eqs
    | Some hss ->
      Debug.assume bol r1 r2;
      if bol then
        add_eq uf hss (embed r1) (embed r2) dep env eqs
      else
        add_diseq uf hss (embed r1) (embed r2) dep env eqs
  in
  Debug.print_env "before assume" env;
  let env, eqs =
    List.fold_left
      (fun (env,eqs) -> function
         | Xliteral.Eq(r1,r2), _, ex, orig ->
           (* needed for models generation because fresh terms are not
              added with function add *)
           let env = add_rec (add_rec env r1) r2 in
           let env, eqs =
             if orig == Th_util.Subst then update_cs_modulo_eq r1 r2 ex env eqs
             else env, eqs
           in
           aux true  r1 r2 ex env eqs (values_of (X.type_info r1))

         | Xliteral.Distinct(false, [r1;r2]), _, ex, _ ->
           (* needed for models generation because fresh terms are not
              added with function add *)
           let env = add_rec (add_rec env r1) r2 in
           aux false r1 r2 ex env eqs (values_of (X.type_info r1))

         | Xliteral.Builtin(true, Sy.IsConstr hs, [e]), _, ex, _ ->
           assume_is_constr uf hs e ex env eqs

         | Xliteral.Builtin(false, Sy.IsConstr hs, [e]), _, ex, _
             [@ocaml.ppwarning "XXX: assume not (. ? .): reasoning missing ?"]
           ->
           assume_not_is_constr uf hs e ex env eqs

         | _ -> env, eqs

      ) (env,[]) la
  in
  let eqs =
    List.fold_left
      (fun eqs (a, ex) -> (Sig_rel.LTerm a, ex, Th_util.Other) :: eqs)
      eqs env.pending_deductions
  in
  let env = {env with pending_deductions = []} in
  Debug.print_env "after assume" env;
  if debug_adt () then begin
    fprintf fmt "[ADT] assume deduced %d equalities@." (List.length eqs);
    List.iter
      (fun (a, _, _) ->
         match a with
         | Sig_rel.LTerm a -> fprintf fmt "  %a@." E.print a;
         | _ -> assert false
      )eqs;
  end;
  env, { Sig_rel.assume = eqs; remove = [] }


(* ################################################################ *)

let two = Numbers.Q.from_int 2
let case_split env uf ~for_model =
  assert (not for_model);
  Debug.print_env "before cs" env;
  try
    let r, mhs = MX.choose env.selectors in
    fprintf fmt "found r = %a@." X.print r;
    let hs, _ = MHs.choose mhs in
    fprintf fmt "found hs = %a@." Hs.print hs;
    (* cs on negative version would be better in general *)
    let cs =  LR.mkv_builtin false (Sy.IsConstr hs) [r] in
    [ cs, true, Th_util.CS(Th_util.Th_adt, two) ]
  with Not_found ->
    Debug.no_case_split ();
    []

let case_split env uf ~for_model =
  []


let query env uf a_ex = None
                            (*
    try ignore(assume env uf [a_ex]); Sig.No
    with Inconsistent (expl, classes) -> Sig.Yes (expl, classes)
                             *)
(* ################################################################ *)
(* ################################################################ *)
(* ################################################################ *)
(***
   type r = X.r
   type uf = Uf.t

   module Sh = Shostak(X)
   open Sh

   module Ex = Explanation

   module MX = Map.Make(struct type t = X.r let compare = X.hash_cmp end)
   module HSS = Set.Make (struct type t=Hs.t let compare = Hs.compare end)


   type t = { mx : (HSS.t * Ex.t) MX.t; classes : E.Set.t list;
           size_splits : Numbers.Q.t }

   let empty classes = { mx = MX.empty; classes = classes;
                      size_splits = Numbers.Q.one }



   let add_eq hss sm1 sm2 dep env eqs =
   match sm1, sm2 with
    | Alien r, Cons(h,ty) | Cons (h,ty), Alien r  ->
      let enum, ex = try MX.find r env.mx with Not_found -> hss, Ex.empty in
      let ex = Ex.union ex dep in
      if not (HSS.mem h enum) then raise (Inconsistent (ex, env.classes));
   {env with mx = MX.add r (HSS.singleton h, ex) env.mx} , eqs

    | Alien r1, Alien r2   ->
      let enum1,ex1 =
        try MX.find r1 env.mx with Not_found -> hss, Ex.empty in
      let enum2,ex2 =
        try MX.find r2 env.mx with Not_found -> hss, Ex.empty in
      let ex = Ex.union dep (Ex.union ex1 ex2) in
      let diff = HSS.inter enum1 enum2 in
      if HSS.is_empty diff then raise (Inconsistent (ex, env.classes));
      let mx = MX.add r1 (diff, ex) env.mx in
      let env = {env with mx = MX.add r2 (diff, ex) mx } in
      if HSS.cardinal diff = 1 then
        let h' = HSS.choose diff in
        let ty = X.type_info r1 in
        env, (LSem (LR.mkv_eq r1 (is_mine (Cons(h',ty)))), ex, Sig.Other)::eqs
      else env, eqs

    |  _ -> env, eqs


   let assume env uf la =
   let env = count_splits env la in
   let classes = Uf.cl_extract uf in
   let env = { env with classes = classes } in
   let aux bol r1 r2 dep env eqs = function
    | None     -> env, eqs
    | Some hss ->
      Debug.assume bol r1 r2;
      if bol then
        add_eq hss (embed r1) (embed r2) dep env eqs
      else
        add_diseq hss (embed r1) (embed r2) dep env eqs
   in
   Debug.print_env env;
   let env, eqs =
    List.fold_left
      (fun (env,eqs) -> function
        | A.Eq(r1,r2), _, ex, _ ->
          (* needed for models generation because fresh terms are not
             added with function add *)
          let env = add_rec (add_rec env r1) r2 in
   aux true  r1 r2 ex env eqs (values_of r1)

        | A.Distinct(false, [r1;r2]), _, ex, _ ->
          (* needed for models generation because fresh terms are not
             added with function add *)
          let env = add_rec (add_rec env r1) r2 in
   aux false r1 r2 ex env eqs (values_of r1)

        | _ -> env, eqs

      ) (env,[]) la
   in
   env, { assume = eqs; remove = [] }

   let add env _ r _ = add_aux env r

   let case_split env uf ~for_model =
   let acc = MX.fold
    (fun r (hss, ex) acc ->
      let sz = HSS.cardinal hss in
      if sz = 1 then acc
      else match acc with
   | Some (n,r,hs) when n <= sz -> acc
   | _ -> Some (sz, r, HSS.choose hss)
    ) env.mx None
   in
   match acc with
   | Some (n,r,hs) ->
    let n = Numbers.Q.from_int n in
    if for_model ||
      Numbers.Q.compare
      (Numbers.Q.mult n env.size_splits) (max_split ()) <= 0  ||
      Numbers.Q.sign  (max_split ()) < 0 then
      let r' = is_mine (Cons(hs,X.type_info r)) in
      Debug.case_split r r';
      [LR.mkv_eq r r', true, CS(Th_sum, n)]
    else []
   | None ->
    Debug.no_case_split ();
    []

   let query env uf a_ex =
   try ignore(assume env uf [a_ex]); Sig.No
   with Inconsistent (expl, classes) -> Sig.Yes (expl, classes)

   let assume env uf la =
   if Options.timers() then
    try
   Timers.exec_timer_start Timers.M_Sum Timers.F_assume;
   let res =assume env uf la in
   Timers.exec_timer_pause Timers.M_Sum Timers.F_assume;
   res
    with e ->
   Timers.exec_timer_pause Timers.M_Sum Timers.F_assume;
   raise e
   else assume env uf la

   let query env uf la =
   if Options.timers() then
    try
   Timers.exec_timer_start Timers.M_Sum Timers.F_query;
   let res = query env uf la  in
   Timers.exec_timer_pause Timers.M_Sum Timers.F_query;
   res
    with e ->
   Timers.exec_timer_pause Timers.M_Sum Timers.F_query;
   raise e
   else query env uf la


   let print_model _ _ _ = ()

   let new_terms env = E.Set.empty

   let instantiate ~do_syntactic_matching _ env uf _  = env, []
   let assume_th_elt t th_elt dep =
   match th_elt.Commands.extends with
   | Typed.Sum ->
    failwith "This Theory does not support theories extension"
   | _ -> t
 ***)
